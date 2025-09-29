// Lean compiler output
// Module: Init.Grind.Injective
// Imports: public import Init.Data.Function public import Init.Classical
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
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__1;
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_leftInvUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__9;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__6;
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__0;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__5;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_leftInvUnexpander(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__2;
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__7;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__8;
static lean_object* l_Lean_Grind_leftInvUnexpander___closed__4;
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Grind_leftInvUnexpander___closed__3;
x_2 = l_Lean_Grind_leftInvUnexpander___closed__2;
x_3 = l_Lean_Grind_leftInvUnexpander___closed__1;
x_4 = l_Lean_Grind_leftInvUnexpander___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_⁻¹", 10, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_leftInvUnexpander___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⁻¹", 5, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_leftInvUnexpander___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_leftInvUnexpander___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_leftInvUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_leftInvUnexpander___closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_10);
x_12 = l_Lean_Syntax_matchesNull(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(3u);
lean_inc(x_10);
x_14 = l_Lean_Syntax_matchesNull(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = l_Lean_Syntax_getArg(x_10, x_8);
x_18 = l_Lean_Syntax_getArg(x_10, x_11);
lean_dec(x_10);
x_19 = l_Lean_SourceInfo_fromRef(x_2, x_12);
x_20 = l_Lean_Grind_leftInvUnexpander___closed__6;
x_21 = l_Lean_Grind_leftInvUnexpander___closed__7;
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_19);
x_23 = l_Lean_Syntax_node2(x_19, x_20, x_17, x_22);
x_24 = l_Lean_Grind_leftInvUnexpander___closed__9;
lean_inc(x_19);
x_25 = l_Lean_Syntax_node1(x_19, x_24, x_18);
x_26 = l_Lean_Syntax_node2(x_19, x_4, x_23, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lean_Syntax_getArg(x_10, x_8);
lean_dec(x_10);
x_29 = 0;
x_30 = l_Lean_SourceInfo_fromRef(x_2, x_29);
x_31 = l_Lean_Grind_leftInvUnexpander___closed__6;
x_32 = l_Lean_Grind_leftInvUnexpander___closed__7;
lean_inc(x_30);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Syntax_node2(x_30, x_31, x_28, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_leftInvUnexpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_leftInvUnexpander(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_Function(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Classical(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Injective(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Function(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_leftInvUnexpander___closed__0 = _init_l_Lean_Grind_leftInvUnexpander___closed__0();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__0);
l_Lean_Grind_leftInvUnexpander___closed__1 = _init_l_Lean_Grind_leftInvUnexpander___closed__1();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__1);
l_Lean_Grind_leftInvUnexpander___closed__2 = _init_l_Lean_Grind_leftInvUnexpander___closed__2();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__2);
l_Lean_Grind_leftInvUnexpander___closed__3 = _init_l_Lean_Grind_leftInvUnexpander___closed__3();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__3);
l_Lean_Grind_leftInvUnexpander___closed__4 = _init_l_Lean_Grind_leftInvUnexpander___closed__4();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__4);
l_Lean_Grind_leftInvUnexpander___closed__5 = _init_l_Lean_Grind_leftInvUnexpander___closed__5();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__5);
l_Lean_Grind_leftInvUnexpander___closed__6 = _init_l_Lean_Grind_leftInvUnexpander___closed__6();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__6);
l_Lean_Grind_leftInvUnexpander___closed__7 = _init_l_Lean_Grind_leftInvUnexpander___closed__7();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__7);
l_Lean_Grind_leftInvUnexpander___closed__8 = _init_l_Lean_Grind_leftInvUnexpander___closed__8();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__8);
l_Lean_Grind_leftInvUnexpander___closed__9 = _init_l_Lean_Grind_leftInvUnexpander___closed__9();
lean_mark_persistent(l_Lean_Grind_leftInvUnexpander___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
