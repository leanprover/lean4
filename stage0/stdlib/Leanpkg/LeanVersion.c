// Lean compiler output
// Module: Leanpkg.LeanVersion
// Imports: Init
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Leanpkg_leanVersionStringCore___closed__2;
lean_object* l_Leanpkg_leanVersionStringCore___closed__9;
lean_object* l_Leanpkg_leanVersionString___closed__4;
lean_object* l_Leanpkg_leanVersionStringCore___closed__8;
lean_object* l_Leanpkg_leanVersionStringCore___closed__6;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Leanpkg_leanVersionStringCore___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Leanpkg_leanVersionStringCore___closed__5;
uint8_t l_Leanpkg_leanVersionString___closed__2;
extern lean_object* l_Lean_version_patch;
extern lean_object* l_Lean_version_specialDesc;
extern lean_object* l_Lean_version_major;
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_Leanpkg_leanVersionString___closed__6;
uint8_t l_Leanpkg_leanVersionString___closed__1;
lean_object* l_Leanpkg_uiLeanVersionString;
lean_object* l_Leanpkg_leanVersionString___closed__8;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Leanpkg_leanVersionString___closed__5;
lean_object* l_Leanpkg_leanVersionStringCore___closed__1;
lean_object* l_Leanpkg_uiLeanVersionString___closed__5;
lean_object* l_Leanpkg_leanVersionString___closed__3;
lean_object* l_Leanpkg_leanVersionStringCore___closed__3;
lean_object* l_Leanpkg_uiLeanVersionString___closed__3;
extern lean_object* l_Lean_version_minor;
extern uint8_t l_Lean_version_isRelease;
lean_object* l_Leanpkg_leanVersionString___closed__7;
lean_object* l_Leanpkg_leanVersionString;
lean_object* l_Leanpkg_uiLeanVersionString___closed__2;
lean_object* l_Leanpkg_leanVersionStringCore;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Leanpkg_leanVersionStringCore___closed__7;
lean_object* l_Leanpkg_uiLeanVersionString___closed__1;
lean_object* l_Leanpkg_uiLeanVersionString___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_version_major;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = l_Leanpkg_leanVersionStringCore___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionStringCore___closed__2;
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_version_minor;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionStringCore___closed__3;
x_2 = l_Leanpkg_leanVersionStringCore___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionStringCore___closed__5;
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_version_patch;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionStringCore___closed__6;
x_2 = l_Leanpkg_leanVersionStringCore___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionStringCore___closed__8;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionStringCore() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_leanVersionStringCore___closed__9;
return x_1;
}
}
static uint8_t _init_l_Leanpkg_leanVersionString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_version_specialDesc;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Leanpkg_leanVersionString___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l_Leanpkg_leanVersionString___closed__1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_leanVersionString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("master");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_leanVersionString___closed__4() {
_start:
{
uint8_t x_1; 
x_1 = l_Leanpkg_leanVersionString___closed__2;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Leanpkg_leanVersionString___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_version_specialDesc;
return x_3;
}
}
}
static lean_object* _init_l_Leanpkg_leanVersionString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leanprover/lean:");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_leanVersionString___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionString___closed__5;
x_2 = l_Leanpkg_leanVersionStringCore;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_leanVersionString___closed__6;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_leanVersionString___closed__8() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Leanpkg_leanVersionString___closed__4;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Leanpkg_leanVersionString___closed__7;
return x_3;
}
}
}
static lean_object* _init_l_Leanpkg_leanVersionString() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_leanVersionString___closed__8;
return x_1;
}
}
static lean_object* _init_l_Leanpkg_uiLeanVersionString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("master (");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_uiLeanVersionString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_uiLeanVersionString___closed__1;
x_2 = l_Leanpkg_leanVersionStringCore;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_uiLeanVersionString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_uiLeanVersionString___closed__2;
x_2 = l_prec_x28___x29___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_uiLeanVersionString___closed__4() {
_start:
{
uint8_t x_1; 
x_1 = l_Leanpkg_leanVersionString___closed__2;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Leanpkg_uiLeanVersionString___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_version_specialDesc;
return x_3;
}
}
}
static lean_object* _init_l_Leanpkg_uiLeanVersionString___closed__5() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Leanpkg_uiLeanVersionString___closed__4;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Leanpkg_leanVersionStringCore;
return x_3;
}
}
}
static lean_object* _init_l_Leanpkg_uiLeanVersionString() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_uiLeanVersionString___closed__5;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Leanpkg_LeanVersion(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Leanpkg_leanVersionStringCore___closed__1 = _init_l_Leanpkg_leanVersionStringCore___closed__1();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__1);
l_Leanpkg_leanVersionStringCore___closed__2 = _init_l_Leanpkg_leanVersionStringCore___closed__2();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__2);
l_Leanpkg_leanVersionStringCore___closed__3 = _init_l_Leanpkg_leanVersionStringCore___closed__3();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__3);
l_Leanpkg_leanVersionStringCore___closed__4 = _init_l_Leanpkg_leanVersionStringCore___closed__4();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__4);
l_Leanpkg_leanVersionStringCore___closed__5 = _init_l_Leanpkg_leanVersionStringCore___closed__5();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__5);
l_Leanpkg_leanVersionStringCore___closed__6 = _init_l_Leanpkg_leanVersionStringCore___closed__6();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__6);
l_Leanpkg_leanVersionStringCore___closed__7 = _init_l_Leanpkg_leanVersionStringCore___closed__7();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__7);
l_Leanpkg_leanVersionStringCore___closed__8 = _init_l_Leanpkg_leanVersionStringCore___closed__8();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__8);
l_Leanpkg_leanVersionStringCore___closed__9 = _init_l_Leanpkg_leanVersionStringCore___closed__9();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore___closed__9);
l_Leanpkg_leanVersionStringCore = _init_l_Leanpkg_leanVersionStringCore();
lean_mark_persistent(l_Leanpkg_leanVersionStringCore);
l_Leanpkg_leanVersionString___closed__1 = _init_l_Leanpkg_leanVersionString___closed__1();
l_Leanpkg_leanVersionString___closed__2 = _init_l_Leanpkg_leanVersionString___closed__2();
l_Leanpkg_leanVersionString___closed__3 = _init_l_Leanpkg_leanVersionString___closed__3();
lean_mark_persistent(l_Leanpkg_leanVersionString___closed__3);
l_Leanpkg_leanVersionString___closed__4 = _init_l_Leanpkg_leanVersionString___closed__4();
lean_mark_persistent(l_Leanpkg_leanVersionString___closed__4);
l_Leanpkg_leanVersionString___closed__5 = _init_l_Leanpkg_leanVersionString___closed__5();
lean_mark_persistent(l_Leanpkg_leanVersionString___closed__5);
l_Leanpkg_leanVersionString___closed__6 = _init_l_Leanpkg_leanVersionString___closed__6();
lean_mark_persistent(l_Leanpkg_leanVersionString___closed__6);
l_Leanpkg_leanVersionString___closed__7 = _init_l_Leanpkg_leanVersionString___closed__7();
lean_mark_persistent(l_Leanpkg_leanVersionString___closed__7);
l_Leanpkg_leanVersionString___closed__8 = _init_l_Leanpkg_leanVersionString___closed__8();
lean_mark_persistent(l_Leanpkg_leanVersionString___closed__8);
l_Leanpkg_leanVersionString = _init_l_Leanpkg_leanVersionString();
lean_mark_persistent(l_Leanpkg_leanVersionString);
l_Leanpkg_uiLeanVersionString___closed__1 = _init_l_Leanpkg_uiLeanVersionString___closed__1();
lean_mark_persistent(l_Leanpkg_uiLeanVersionString___closed__1);
l_Leanpkg_uiLeanVersionString___closed__2 = _init_l_Leanpkg_uiLeanVersionString___closed__2();
lean_mark_persistent(l_Leanpkg_uiLeanVersionString___closed__2);
l_Leanpkg_uiLeanVersionString___closed__3 = _init_l_Leanpkg_uiLeanVersionString___closed__3();
lean_mark_persistent(l_Leanpkg_uiLeanVersionString___closed__3);
l_Leanpkg_uiLeanVersionString___closed__4 = _init_l_Leanpkg_uiLeanVersionString___closed__4();
lean_mark_persistent(l_Leanpkg_uiLeanVersionString___closed__4);
l_Leanpkg_uiLeanVersionString___closed__5 = _init_l_Leanpkg_uiLeanVersionString___closed__5();
lean_mark_persistent(l_Leanpkg_uiLeanVersionString___closed__5);
l_Leanpkg_uiLeanVersionString = _init_l_Leanpkg_uiLeanVersionString();
lean_mark_persistent(l_Leanpkg_uiLeanVersionString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
