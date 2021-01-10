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
uint8_t l_Lean_Elab_getAutoBoundImplicitLocalOption(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object*);
uint8_t l_String_anyAux_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_Elab_isValidAutoBoundLevelName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_isValidAutoBoundImplicitName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__3;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___lambda__1___boxed(lean_object*);
uint8_t l_Lean_isNumericSubscript(uint32_t);
uint8_t l_Char_isLower(uint32_t);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__1;
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2;
lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_488____closed__3;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral(lean_object*);
lean_object* l_Lean_Elab_isValidAutoBoundImplicitName_match__1(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__4;
lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___boxed(lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*);
lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object*);
uint8_t l_Lean_isGreek(uint32_t);
uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___lambda__1(uint32_t);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3_(lean_object*);
lean_object* l_Lean_Elab_isValidAutoBoundLevelName_match__1(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object*);
lean_object* l_Lean_Elab_getAutoBoundImplicitLocalOption___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("autoBoundImplicitLocal");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unbound local variables in declaration headers become implicit arguments if they are a lower case or greek letter followed by numeric digits. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Data_Options___hyg_488____closed__3;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__4;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Lean_Elab_getAutoBoundImplicitLocalOption(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_getAutoBoundImplicitLocalOption___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_getAutoBoundImplicitLocalOption(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___lambda__1(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isDigit(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_isNumericSubscript(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
static lean_object* _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___lambda__1___boxed), 1, 0);
return x_1;
}
}
uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___closed__1;
x_6 = l_String_anyAux_loop(x_2, x_4, x_5, x_3);
lean_dec(x_4);
lean_dec(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_isValidAutoBoundImplicitName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_2(x_2, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Elab_isValidAutoBoundImplicitName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_isValidAutoBoundImplicitName_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_length(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
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
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_string_utf8_byte_size(x_3);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Substring_nextn(x_13, x_14, x_5);
lean_dec(x_13);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_12);
x_17 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral(x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_string_utf8_byte_size(x_3);
lean_inc(x_18);
lean_inc(x_3);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Substring_nextn(x_19, x_20, x_5);
lean_dec(x_19);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
x_23 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral(x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isValidAutoBoundImplicitName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_isValidAutoBoundLevelName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_2(x_2, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Elab_isValidAutoBoundLevelName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_isValidAutoBoundLevelName_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_length(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
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
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_string_utf8_byte_size(x_3);
lean_inc(x_11);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Substring_nextn(x_12, x_13, x_5);
lean_dec(x_12);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_11);
x_16 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral(x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isValidAutoBoundLevelName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Options(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_AutoBound(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3____closed__4);
res = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___closed__1 = _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___closed__1();
lean_mark_persistent(l___private_Lean_Elab_AutoBound_0__Lean_Elab_allNumeral___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
