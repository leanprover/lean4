// Lean compiler output
// Module: Init.Grind.Util
// Imports: Init.Core
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
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_eqMatchUnexpander___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__8;
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__9;
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___rarg(lean_object*);
static lean_object* l_Lean_Grind_offsetUnexpander___closed__2;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_offset(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_offsetUnexpander___closed__1;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_eqMatchUnexpander___closed__2;
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_offsetUnexpander___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__6;
LEAN_EXPORT lean_object* l_Lean_Grind_offset___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_eqMatchUnexpander___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__2;
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__4;
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__5;
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__7;
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_nestedProofUnexpander___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_simpMatchDiscrsOnly___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_simpMatchDiscrsOnly___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_offset(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Grind_nestedProofUnexpander___closed__1;
x_2 = l_Lean_Grind_nestedProofUnexpander___closed__2;
x_3 = l_Lean_Grind_nestedProofUnexpander___closed__3;
x_4 = l_Lean_Grind_nestedProofUnexpander___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term‹_›", 11, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Grind_nestedProofUnexpander___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("‹", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_nestedProofUnexpander___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("›", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_nestedProofUnexpander___closed__5;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_Syntax_matchesNull(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
lean_dec(x_9);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_2, x_15);
x_17 = l_Lean_Grind_nestedProofUnexpander___closed__8;
lean_inc(x_16);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Grind_nestedProofUnexpander___closed__9;
lean_inc(x_16);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Grind_nestedProofUnexpander___closed__7;
x_22 = l_Lean_Syntax_node3(x_16, x_21, x_18, x_14, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_nestedProofUnexpander(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_nestedProofUnexpander___closed__5;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_Syntax_matchesNull(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_matchCondUnexpander(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_eqMatchUnexpander___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_=_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_eqMatchUnexpander___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Grind_eqMatchUnexpander___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_eqMatchUnexpander___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_nestedProofUnexpander___closed__5;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_2, x_17);
x_19 = l_Lean_Grind_eqMatchUnexpander___closed__3;
lean_inc(x_18);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Grind_eqMatchUnexpander___closed__2;
x_22 = l_Lean_Syntax_node3(x_18, x_21, x_15, x_20, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_eqMatchUnexpander(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_offsetUnexpander___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_+_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_offsetUnexpander___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Grind_offsetUnexpander___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_offsetUnexpander___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_nestedProofUnexpander___closed__5;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_2, x_17);
x_19 = l_Lean_Grind_offsetUnexpander___closed__3;
lean_inc(x_18);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Grind_offsetUnexpander___closed__2;
x_22 = l_Lean_Syntax_node3(x_18, x_21, x_15, x_20, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_offsetUnexpander(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_nestedProofUnexpander___closed__1 = _init_l_Lean_Grind_nestedProofUnexpander___closed__1();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__1);
l_Lean_Grind_nestedProofUnexpander___closed__2 = _init_l_Lean_Grind_nestedProofUnexpander___closed__2();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__2);
l_Lean_Grind_nestedProofUnexpander___closed__3 = _init_l_Lean_Grind_nestedProofUnexpander___closed__3();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__3);
l_Lean_Grind_nestedProofUnexpander___closed__4 = _init_l_Lean_Grind_nestedProofUnexpander___closed__4();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__4);
l_Lean_Grind_nestedProofUnexpander___closed__5 = _init_l_Lean_Grind_nestedProofUnexpander___closed__5();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__5);
l_Lean_Grind_nestedProofUnexpander___closed__6 = _init_l_Lean_Grind_nestedProofUnexpander___closed__6();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__6);
l_Lean_Grind_nestedProofUnexpander___closed__7 = _init_l_Lean_Grind_nestedProofUnexpander___closed__7();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__7);
l_Lean_Grind_nestedProofUnexpander___closed__8 = _init_l_Lean_Grind_nestedProofUnexpander___closed__8();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__8);
l_Lean_Grind_nestedProofUnexpander___closed__9 = _init_l_Lean_Grind_nestedProofUnexpander___closed__9();
lean_mark_persistent(l_Lean_Grind_nestedProofUnexpander___closed__9);
l_Lean_Grind_eqMatchUnexpander___closed__1 = _init_l_Lean_Grind_eqMatchUnexpander___closed__1();
lean_mark_persistent(l_Lean_Grind_eqMatchUnexpander___closed__1);
l_Lean_Grind_eqMatchUnexpander___closed__2 = _init_l_Lean_Grind_eqMatchUnexpander___closed__2();
lean_mark_persistent(l_Lean_Grind_eqMatchUnexpander___closed__2);
l_Lean_Grind_eqMatchUnexpander___closed__3 = _init_l_Lean_Grind_eqMatchUnexpander___closed__3();
lean_mark_persistent(l_Lean_Grind_eqMatchUnexpander___closed__3);
l_Lean_Grind_offsetUnexpander___closed__1 = _init_l_Lean_Grind_offsetUnexpander___closed__1();
lean_mark_persistent(l_Lean_Grind_offsetUnexpander___closed__1);
l_Lean_Grind_offsetUnexpander___closed__2 = _init_l_Lean_Grind_offsetUnexpander___closed__2();
lean_mark_persistent(l_Lean_Grind_offsetUnexpander___closed__2);
l_Lean_Grind_offsetUnexpander___closed__3 = _init_l_Lean_Grind_offsetUnexpander___closed__3();
lean_mark_persistent(l_Lean_Grind_offsetUnexpander___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
