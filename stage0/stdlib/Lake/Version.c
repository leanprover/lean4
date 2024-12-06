// Lean compiler output
// Module: Lake.Version
// Imports: Init.Data.ToString
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_version_specialDesc___closed__5;
static lean_object* l_Lake_uiVersionString___closed__4;
static lean_object* l_Lake_uiVersionString___closed__1;
LEAN_EXPORT lean_object* l_Lake_versionStringCore;
extern lean_object* l_Lean_githash;
static lean_object* l_Lake_uiVersionString___closed__7;
static lean_object* l_Lake_versionString___closed__4;
static lean_object* l_Lake_versionStringCore___closed__8;
static lean_object* l_Lake_uiVersionString___closed__3;
static lean_object* l_Lake_versionStringCore___closed__7;
static lean_object* l_Lake_version_specialDesc___closed__4;
LEAN_EXPORT lean_object* l_Lake_version_specialDesc;
LEAN_EXPORT lean_object* l_Lake_versionString;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static uint8_t l_Lake_version_specialDesc___closed__3;
extern uint8_t l_Lean_version_isRelease;
static lean_object* l_Lake_versionStringCore___closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_versionStringCore___closed__5;
static lean_object* l_Lake_versionStringCore___closed__10;
static lean_object* l_Lake_versionStringCore___closed__1;
static lean_object* l_Lake_version_specialDesc___closed__7;
static lean_object* l_Lake_versionStringCore___closed__6;
static lean_object* l_Lake_uiVersionString___closed__5;
uint8_t l_instDecidableNot___rarg(uint8_t);
static uint8_t l_Lake_versionString___closed__1;
static lean_object* l_Lake_version_specialDesc___closed__1;
static lean_object* l_Lake_version_specialDesc___closed__2;
extern lean_object* l_Lean_versionString;
static lean_object* l_Lake_versionStringCore___closed__4;
static lean_object* l_Lake_versionStringCore___closed__3;
static lean_object* l_Lake_version_specialDesc___closed__8;
static lean_object* l_Lake_versionString___closed__6;
LEAN_EXPORT lean_object* l_Lake_version_patch;
static lean_object* l_Lake_versionString___closed__7;
static lean_object* l_Lake_version_specialDesc___closed__6;
static lean_object* l_Lake_versionString___closed__8;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_version_minor;
LEAN_EXPORT uint8_t l_Lake_version_isRelease;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_versionStringCore___closed__2;
static lean_object* l_Lake_versionString___closed__3;
static lean_object* l_Lake_uiVersionString___closed__2;
LEAN_EXPORT lean_object* l_Lake_version_major;
static uint8_t l_Lake_versionString___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_versionStringCore___closed__11;
static lean_object* l_Lake_version_specialDesc___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_versionString___closed__5;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uiVersionString;
static lean_object* l_Lake_uiVersionString___closed__6;
static lean_object* _init_l_Lake_version_major() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(5u);
return x_1;
}
}
static lean_object* _init_l_Lake_version_minor() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lake_version_patch() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static uint8_t _init_l_Lake_version_isRelease() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
return x_1;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("src", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_githash;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_version_specialDesc___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_version_specialDesc___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_githash;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_version_specialDesc___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_version_specialDesc___closed__4;
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Substring_nextn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_version_specialDesc___closed__5;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_githash;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_version_specialDesc___closed__6;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__8() {
_start:
{
uint8_t x_1; 
x_1 = l_Lake_version_specialDesc___closed__3;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_version_specialDesc___closed__7;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_version_specialDesc___closed__1;
return x_3;
}
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__9() {
_start:
{
uint8_t x_1; 
x_1 = l_Lake_version_isRelease;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_version_specialDesc___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_version_specialDesc___closed__8;
return x_3;
}
}
}
static lean_object* _init_l_Lake_version_specialDesc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_version_specialDesc___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_version_major;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__2;
x_2 = l_Lake_versionStringCore___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__3;
x_2 = l_Lake_versionStringCore___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_version_minor;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__5;
x_2 = l_Lake_versionStringCore___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__7;
x_2 = l_Lake_versionStringCore___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_version_patch;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__8;
x_2 = l_Lake_versionStringCore___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__10;
x_2 = l_Lake_versionStringCore___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_versionStringCore___closed__11;
return x_1;
}
}
static uint8_t _init_l_Lake_versionString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_version_specialDesc;
x_2 = l_Lake_versionStringCore___closed__2;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Lake_versionString___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l_Lake_versionString___closed__1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_versionString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionStringCore___closed__2;
x_2 = l_Lake_versionStringCore;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_versionString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionString___closed__3;
x_2 = l_Lake_versionString___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionString___closed__5;
x_2 = l_Lake_version_specialDesc;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionString___closed__6;
x_2 = l_Lake_versionStringCore___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString___closed__8() {
_start:
{
uint8_t x_1; 
x_1 = l_Lake_versionString___closed__2;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_versionStringCore;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_versionString___closed__7;
return x_3;
}
}
}
static lean_object* _init_l_Lake_versionString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_versionString___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake version ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uiVersionString___closed__1;
x_2 = l_Lake_versionString;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (Lean version ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uiVersionString___closed__2;
x_2 = l_Lake_uiVersionString___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uiVersionString___closed__4;
x_2 = l_Lean_versionString;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uiVersionString___closed__5;
x_2 = l_Lake_uiVersionString___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_uiVersionString___closed__7;
return x_1;
}
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Version(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_version_major = _init_l_Lake_version_major();
lean_mark_persistent(l_Lake_version_major);
l_Lake_version_minor = _init_l_Lake_version_minor();
lean_mark_persistent(l_Lake_version_minor);
l_Lake_version_patch = _init_l_Lake_version_patch();
lean_mark_persistent(l_Lake_version_patch);
l_Lake_version_isRelease = _init_l_Lake_version_isRelease();
l_Lake_version_specialDesc___closed__1 = _init_l_Lake_version_specialDesc___closed__1();
lean_mark_persistent(l_Lake_version_specialDesc___closed__1);
l_Lake_version_specialDesc___closed__2 = _init_l_Lake_version_specialDesc___closed__2();
lean_mark_persistent(l_Lake_version_specialDesc___closed__2);
l_Lake_version_specialDesc___closed__3 = _init_l_Lake_version_specialDesc___closed__3();
l_Lake_version_specialDesc___closed__4 = _init_l_Lake_version_specialDesc___closed__4();
lean_mark_persistent(l_Lake_version_specialDesc___closed__4);
l_Lake_version_specialDesc___closed__5 = _init_l_Lake_version_specialDesc___closed__5();
lean_mark_persistent(l_Lake_version_specialDesc___closed__5);
l_Lake_version_specialDesc___closed__6 = _init_l_Lake_version_specialDesc___closed__6();
lean_mark_persistent(l_Lake_version_specialDesc___closed__6);
l_Lake_version_specialDesc___closed__7 = _init_l_Lake_version_specialDesc___closed__7();
lean_mark_persistent(l_Lake_version_specialDesc___closed__7);
l_Lake_version_specialDesc___closed__8 = _init_l_Lake_version_specialDesc___closed__8();
lean_mark_persistent(l_Lake_version_specialDesc___closed__8);
l_Lake_version_specialDesc___closed__9 = _init_l_Lake_version_specialDesc___closed__9();
lean_mark_persistent(l_Lake_version_specialDesc___closed__9);
l_Lake_version_specialDesc = _init_l_Lake_version_specialDesc();
lean_mark_persistent(l_Lake_version_specialDesc);
l_Lake_versionStringCore___closed__1 = _init_l_Lake_versionStringCore___closed__1();
lean_mark_persistent(l_Lake_versionStringCore___closed__1);
l_Lake_versionStringCore___closed__2 = _init_l_Lake_versionStringCore___closed__2();
lean_mark_persistent(l_Lake_versionStringCore___closed__2);
l_Lake_versionStringCore___closed__3 = _init_l_Lake_versionStringCore___closed__3();
lean_mark_persistent(l_Lake_versionStringCore___closed__3);
l_Lake_versionStringCore___closed__4 = _init_l_Lake_versionStringCore___closed__4();
lean_mark_persistent(l_Lake_versionStringCore___closed__4);
l_Lake_versionStringCore___closed__5 = _init_l_Lake_versionStringCore___closed__5();
lean_mark_persistent(l_Lake_versionStringCore___closed__5);
l_Lake_versionStringCore___closed__6 = _init_l_Lake_versionStringCore___closed__6();
lean_mark_persistent(l_Lake_versionStringCore___closed__6);
l_Lake_versionStringCore___closed__7 = _init_l_Lake_versionStringCore___closed__7();
lean_mark_persistent(l_Lake_versionStringCore___closed__7);
l_Lake_versionStringCore___closed__8 = _init_l_Lake_versionStringCore___closed__8();
lean_mark_persistent(l_Lake_versionStringCore___closed__8);
l_Lake_versionStringCore___closed__9 = _init_l_Lake_versionStringCore___closed__9();
lean_mark_persistent(l_Lake_versionStringCore___closed__9);
l_Lake_versionStringCore___closed__10 = _init_l_Lake_versionStringCore___closed__10();
lean_mark_persistent(l_Lake_versionStringCore___closed__10);
l_Lake_versionStringCore___closed__11 = _init_l_Lake_versionStringCore___closed__11();
lean_mark_persistent(l_Lake_versionStringCore___closed__11);
l_Lake_versionStringCore = _init_l_Lake_versionStringCore();
lean_mark_persistent(l_Lake_versionStringCore);
l_Lake_versionString___closed__1 = _init_l_Lake_versionString___closed__1();
l_Lake_versionString___closed__2 = _init_l_Lake_versionString___closed__2();
l_Lake_versionString___closed__3 = _init_l_Lake_versionString___closed__3();
lean_mark_persistent(l_Lake_versionString___closed__3);
l_Lake_versionString___closed__4 = _init_l_Lake_versionString___closed__4();
lean_mark_persistent(l_Lake_versionString___closed__4);
l_Lake_versionString___closed__5 = _init_l_Lake_versionString___closed__5();
lean_mark_persistent(l_Lake_versionString___closed__5);
l_Lake_versionString___closed__6 = _init_l_Lake_versionString___closed__6();
lean_mark_persistent(l_Lake_versionString___closed__6);
l_Lake_versionString___closed__7 = _init_l_Lake_versionString___closed__7();
lean_mark_persistent(l_Lake_versionString___closed__7);
l_Lake_versionString___closed__8 = _init_l_Lake_versionString___closed__8();
lean_mark_persistent(l_Lake_versionString___closed__8);
l_Lake_versionString = _init_l_Lake_versionString();
lean_mark_persistent(l_Lake_versionString);
l_Lake_uiVersionString___closed__1 = _init_l_Lake_uiVersionString___closed__1();
lean_mark_persistent(l_Lake_uiVersionString___closed__1);
l_Lake_uiVersionString___closed__2 = _init_l_Lake_uiVersionString___closed__2();
lean_mark_persistent(l_Lake_uiVersionString___closed__2);
l_Lake_uiVersionString___closed__3 = _init_l_Lake_uiVersionString___closed__3();
lean_mark_persistent(l_Lake_uiVersionString___closed__3);
l_Lake_uiVersionString___closed__4 = _init_l_Lake_uiVersionString___closed__4();
lean_mark_persistent(l_Lake_uiVersionString___closed__4);
l_Lake_uiVersionString___closed__5 = _init_l_Lake_uiVersionString___closed__5();
lean_mark_persistent(l_Lake_uiVersionString___closed__5);
l_Lake_uiVersionString___closed__6 = _init_l_Lake_uiVersionString___closed__6();
lean_mark_persistent(l_Lake_uiVersionString___closed__6);
l_Lake_uiVersionString___closed__7 = _init_l_Lake_uiVersionString___closed__7();
lean_mark_persistent(l_Lake_uiVersionString___closed__7);
l_Lake_uiVersionString = _init_l_Lake_uiVersionString();
lean_mark_persistent(l_Lake_uiVersionString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
