// Lean compiler output
// Module: Init.Grind.Lint
// Imports: public import Init.Grind.Interactive public import Init.Grind.Config
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
static lean_object* l_Lean_Grind_grindLintInspect___closed__6;
LEAN_EXPORT lean_object* l_Lean_Grind_grindLintMute;
LEAN_EXPORT lean_object* l_Lean_Grind_grindLintInspect;
static lean_object* l_Lean_Grind_grindLintSkip___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_grindLintSkip;
static lean_object* l_Lean_Grind_grindLintSkip___closed__5;
static lean_object* l_Lean_Grind_grindLintCheck___closed__12;
static lean_object* l_Lean_Grind_grindLintCheck___closed__15;
static lean_object* l_Lean_Grind_grindLintCheck___closed__37;
static lean_object* l_Lean_Grind_grindLintCheck___closed__35;
static lean_object* l_Lean_Grind_grindLintSkip___closed__0;
static lean_object* l_Lean_Grind_grindLintInspect___closed__1;
static lean_object* l_Lean_Grind_grindLintCheck___closed__18;
static lean_object* l_Lean_Grind_grindLintSkip___closed__6;
static lean_object* l_Lean_Grind_grindLintCheck___closed__4;
static lean_object* l_Lean_Grind_grindLintCheck___closed__8;
static lean_object* l_Lean_Grind_grindLintInspect___closed__7;
static lean_object* l_Lean_Grind_grindLintCheck___closed__31;
static lean_object* l_Lean_Grind_grindLintInspect___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_grindLintCheck___closed__25;
static lean_object* l_Lean_Grind_grindLintCheck___closed__5;
static lean_object* l_Lean_Grind_grindLintMute___closed__3;
static lean_object* l_Lean_Grind_grindLintCheck___closed__19;
static lean_object* l_Lean_Grind_grindLintCheck___closed__26;
static lean_object* l_Lean_Grind_grindLintCheck___closed__30;
static lean_object* l_Lean_Grind_grindLintCheck___closed__23;
static lean_object* l_Lean_Grind_grindLintCheck___closed__3;
static lean_object* l_Lean_Grind_grindLintSkip___closed__10;
static lean_object* l_Lean_Grind_grindLintInspect___closed__2;
static lean_object* l_Lean_Grind_grindLintCheck___closed__9;
static lean_object* l_Lean_Grind_grindLintCheck___closed__32;
static lean_object* l_Lean_Grind_grindLintCheck___closed__21;
static lean_object* l_Lean_Grind_grindLintCheck___closed__6;
static lean_object* l_Lean_Grind_grindLintInspect___closed__3;
static lean_object* l_Lean_Grind_grindLintCheck___closed__36;
static lean_object* l_Lean_Grind_grindLintCheck___closed__17;
extern lean_object* l_Lean_Parser_Tactic_configItem;
static lean_object* l_Lean_Grind_grindLintCheck___closed__29;
static lean_object* l_Lean_Grind_grindLintMute___closed__0;
static lean_object* l_Lean_Grind_grindLintCheck___closed__1;
static lean_object* l_Lean_Grind_grindLintCheck___closed__10;
static lean_object* l_Lean_Grind_grindLintCheck___closed__27;
static lean_object* l_Lean_Grind_grindLintCheck___closed__24;
static lean_object* l_Lean_Grind_grindLintCheck___closed__0;
static lean_object* l_Lean_Grind_grindLintCheck___closed__11;
static lean_object* l_Lean_Grind_grindLintSkip___closed__7;
static lean_object* l_Lean_Grind_grindLintMute___closed__1;
static lean_object* l_Lean_Grind_grindLintSkip___closed__2;
static lean_object* l_Lean_Grind_grindLintInspect___closed__0;
static lean_object* l_Lean_Grind_grindLintMute___closed__4;
static lean_object* l_Lean_Grind_grindLintCheck___closed__33;
static lean_object* l_Lean_Grind_grindLintCheck___closed__38;
static lean_object* l_Lean_Grind_grindLintMute___closed__5;
static lean_object* l_Lean_Grind_grindLintSkip___closed__4;
static lean_object* l_Lean_Grind_grindLintSkip___closed__11;
static lean_object* l_Lean_Grind_grindLintSkip___closed__8;
static lean_object* l_Lean_Grind_grindLintInspect___closed__5;
static lean_object* l_Lean_Grind_grindLintCheck___closed__39;
static lean_object* l_Lean_Grind_grindLintCheck___closed__2;
static lean_object* l_Lean_Grind_grindLintSkip___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Grind_grindLintCheck___closed__28;
static lean_object* l_Lean_Grind_grindLintCheck___closed__13;
static lean_object* l_Lean_Grind_grindLintCheck___closed__34;
static lean_object* l_Lean_Grind_grindLintCheck___closed__16;
LEAN_EXPORT lean_object* l_Lean_Grind_grindLintCheck;
static lean_object* l_Lean_Grind_grindLintMute___closed__6;
static lean_object* l_Lean_Grind_grindLintCheck___closed__22;
static lean_object* l_Lean_Grind_grindLintSkip___closed__9;
static lean_object* l_Lean_Grind_grindLintCheck___closed__14;
static lean_object* l_Lean_Grind_grindLintCheck___closed__20;
static lean_object* l_Lean_Grind_grindLintMute___closed__2;
static lean_object* l_Lean_Grind_grindLintCheck___closed__7;
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLintCheck", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__2;
x_2 = l_Lean_Grind_grindLintCheck___closed__1;
x_3 = l_Lean_Grind_grindLintCheck___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#grind_lint", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppSpace", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__10;
x_2 = l_Lean_Grind_grindLintCheck___closed__7;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Grind_grindLintCheck___closed__12;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__13;
x_2 = l_Lean_Grind_grindLintCheck___closed__11;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_configItem;
x_2 = l_Lean_Grind_grindLintCheck___closed__10;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_grindLintCheck___closed__17;
x_2 = l_Lean_Grind_grindLintCheck___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__18;
x_2 = l_Lean_Grind_grindLintCheck___closed__14;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optional", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__20;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("in", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__22;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__23;
x_2 = l_Lean_Grind_grindLintCheck___closed__10;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__26() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Grind_grindLintCheck___closed__25;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__26;
x_2 = l_Lean_Grind_grindLintCheck___closed__10;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_grindLintCheck___closed__27;
x_2 = l_Lean_Grind_grindLintCheck___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__28;
x_2 = l_Lean_Grind_grindLintCheck___closed__24;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many1", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__30;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__32;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_grindLintCheck___closed__33;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_grindLintCheck___closed__34;
x_2 = l_Lean_Grind_grindLintCheck___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__35;
x_2 = l_Lean_Grind_grindLintCheck___closed__29;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_grindLintCheck___closed__36;
x_2 = l_Lean_Grind_grindLintCheck___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__37;
x_2 = l_Lean_Grind_grindLintCheck___closed__19;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__38;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Grind_grindLintCheck___closed__3;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_grindLintCheck___closed__39;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLintInspect", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintInspect___closed__0;
x_2 = l_Lean_Grind_grindLintCheck___closed__1;
x_3 = l_Lean_Grind_grindLintCheck___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inspect", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Grind_grindLintInspect___closed__2;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintInspect___closed__3;
x_2 = l_Lean_Grind_grindLintCheck___closed__11;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__18;
x_2 = l_Lean_Grind_grindLintInspect___closed__4;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__35;
x_2 = l_Lean_Grind_grindLintInspect___closed__5;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintInspect___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Grind_grindLintInspect___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_grindLintInspect___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLintMute", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintMute___closed__0;
x_2 = l_Lean_Grind_grindLintCheck___closed__1;
x_3 = l_Lean_Grind_grindLintCheck___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mute", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Grind_grindLintMute___closed__2;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintMute___closed__3;
x_2 = l_Lean_Grind_grindLintCheck___closed__11;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__35;
x_2 = l_Lean_Grind_grindLintMute___closed__4;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintMute___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Grind_grindLintMute___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintMute() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_grindLintMute___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLintSkip", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintSkip___closed__0;
x_2 = l_Lean_Grind_grindLintCheck___closed__1;
x_3 = l_Lean_Grind_grindLintCheck___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skip", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Grind_grindLintSkip___closed__2;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintSkip___closed__3;
x_2 = l_Lean_Grind_grindLintCheck___closed__11;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("suffix", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Grind_grindLintSkip___closed__5;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintSkip___closed__6;
x_2 = l_Lean_Grind_grindLintCheck___closed__10;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_grindLintSkip___closed__7;
x_2 = l_Lean_Grind_grindLintCheck___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintSkip___closed__8;
x_2 = l_Lean_Grind_grindLintSkip___closed__4;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintCheck___closed__35;
x_2 = l_Lean_Grind_grindLintSkip___closed__9;
x_3 = l_Lean_Grind_grindLintCheck___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_grindLintSkip___closed__10;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Grind_grindLintSkip___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_grindLintSkip() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_grindLintSkip___closed__11;
return x_1;
}
}
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
lean_object* initialize_Init_Grind_Config(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_grindLintCheck___closed__0 = _init_l_Lean_Grind_grindLintCheck___closed__0();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__0);
l_Lean_Grind_grindLintCheck___closed__1 = _init_l_Lean_Grind_grindLintCheck___closed__1();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__1);
l_Lean_Grind_grindLintCheck___closed__2 = _init_l_Lean_Grind_grindLintCheck___closed__2();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__2);
l_Lean_Grind_grindLintCheck___closed__3 = _init_l_Lean_Grind_grindLintCheck___closed__3();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__3);
l_Lean_Grind_grindLintCheck___closed__4 = _init_l_Lean_Grind_grindLintCheck___closed__4();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__4);
l_Lean_Grind_grindLintCheck___closed__5 = _init_l_Lean_Grind_grindLintCheck___closed__5();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__5);
l_Lean_Grind_grindLintCheck___closed__6 = _init_l_Lean_Grind_grindLintCheck___closed__6();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__6);
l_Lean_Grind_grindLintCheck___closed__7 = _init_l_Lean_Grind_grindLintCheck___closed__7();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__7);
l_Lean_Grind_grindLintCheck___closed__8 = _init_l_Lean_Grind_grindLintCheck___closed__8();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__8);
l_Lean_Grind_grindLintCheck___closed__9 = _init_l_Lean_Grind_grindLintCheck___closed__9();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__9);
l_Lean_Grind_grindLintCheck___closed__10 = _init_l_Lean_Grind_grindLintCheck___closed__10();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__10);
l_Lean_Grind_grindLintCheck___closed__11 = _init_l_Lean_Grind_grindLintCheck___closed__11();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__11);
l_Lean_Grind_grindLintCheck___closed__12 = _init_l_Lean_Grind_grindLintCheck___closed__12();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__12);
l_Lean_Grind_grindLintCheck___closed__13 = _init_l_Lean_Grind_grindLintCheck___closed__13();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__13);
l_Lean_Grind_grindLintCheck___closed__14 = _init_l_Lean_Grind_grindLintCheck___closed__14();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__14);
l_Lean_Grind_grindLintCheck___closed__15 = _init_l_Lean_Grind_grindLintCheck___closed__15();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__15);
l_Lean_Grind_grindLintCheck___closed__16 = _init_l_Lean_Grind_grindLintCheck___closed__16();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__16);
l_Lean_Grind_grindLintCheck___closed__17 = _init_l_Lean_Grind_grindLintCheck___closed__17();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__17);
l_Lean_Grind_grindLintCheck___closed__18 = _init_l_Lean_Grind_grindLintCheck___closed__18();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__18);
l_Lean_Grind_grindLintCheck___closed__19 = _init_l_Lean_Grind_grindLintCheck___closed__19();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__19);
l_Lean_Grind_grindLintCheck___closed__20 = _init_l_Lean_Grind_grindLintCheck___closed__20();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__20);
l_Lean_Grind_grindLintCheck___closed__21 = _init_l_Lean_Grind_grindLintCheck___closed__21();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__21);
l_Lean_Grind_grindLintCheck___closed__22 = _init_l_Lean_Grind_grindLintCheck___closed__22();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__22);
l_Lean_Grind_grindLintCheck___closed__23 = _init_l_Lean_Grind_grindLintCheck___closed__23();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__23);
l_Lean_Grind_grindLintCheck___closed__24 = _init_l_Lean_Grind_grindLintCheck___closed__24();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__24);
l_Lean_Grind_grindLintCheck___closed__25 = _init_l_Lean_Grind_grindLintCheck___closed__25();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__25);
l_Lean_Grind_grindLintCheck___closed__26 = _init_l_Lean_Grind_grindLintCheck___closed__26();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__26);
l_Lean_Grind_grindLintCheck___closed__27 = _init_l_Lean_Grind_grindLintCheck___closed__27();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__27);
l_Lean_Grind_grindLintCheck___closed__28 = _init_l_Lean_Grind_grindLintCheck___closed__28();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__28);
l_Lean_Grind_grindLintCheck___closed__29 = _init_l_Lean_Grind_grindLintCheck___closed__29();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__29);
l_Lean_Grind_grindLintCheck___closed__30 = _init_l_Lean_Grind_grindLintCheck___closed__30();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__30);
l_Lean_Grind_grindLintCheck___closed__31 = _init_l_Lean_Grind_grindLintCheck___closed__31();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__31);
l_Lean_Grind_grindLintCheck___closed__32 = _init_l_Lean_Grind_grindLintCheck___closed__32();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__32);
l_Lean_Grind_grindLintCheck___closed__33 = _init_l_Lean_Grind_grindLintCheck___closed__33();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__33);
l_Lean_Grind_grindLintCheck___closed__34 = _init_l_Lean_Grind_grindLintCheck___closed__34();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__34);
l_Lean_Grind_grindLintCheck___closed__35 = _init_l_Lean_Grind_grindLintCheck___closed__35();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__35);
l_Lean_Grind_grindLintCheck___closed__36 = _init_l_Lean_Grind_grindLintCheck___closed__36();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__36);
l_Lean_Grind_grindLintCheck___closed__37 = _init_l_Lean_Grind_grindLintCheck___closed__37();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__37);
l_Lean_Grind_grindLintCheck___closed__38 = _init_l_Lean_Grind_grindLintCheck___closed__38();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__38);
l_Lean_Grind_grindLintCheck___closed__39 = _init_l_Lean_Grind_grindLintCheck___closed__39();
lean_mark_persistent(l_Lean_Grind_grindLintCheck___closed__39);
l_Lean_Grind_grindLintCheck = _init_l_Lean_Grind_grindLintCheck();
lean_mark_persistent(l_Lean_Grind_grindLintCheck);
l_Lean_Grind_grindLintInspect___closed__0 = _init_l_Lean_Grind_grindLintInspect___closed__0();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__0);
l_Lean_Grind_grindLintInspect___closed__1 = _init_l_Lean_Grind_grindLintInspect___closed__1();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__1);
l_Lean_Grind_grindLintInspect___closed__2 = _init_l_Lean_Grind_grindLintInspect___closed__2();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__2);
l_Lean_Grind_grindLintInspect___closed__3 = _init_l_Lean_Grind_grindLintInspect___closed__3();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__3);
l_Lean_Grind_grindLintInspect___closed__4 = _init_l_Lean_Grind_grindLintInspect___closed__4();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__4);
l_Lean_Grind_grindLintInspect___closed__5 = _init_l_Lean_Grind_grindLintInspect___closed__5();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__5);
l_Lean_Grind_grindLintInspect___closed__6 = _init_l_Lean_Grind_grindLintInspect___closed__6();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__6);
l_Lean_Grind_grindLintInspect___closed__7 = _init_l_Lean_Grind_grindLintInspect___closed__7();
lean_mark_persistent(l_Lean_Grind_grindLintInspect___closed__7);
l_Lean_Grind_grindLintInspect = _init_l_Lean_Grind_grindLintInspect();
lean_mark_persistent(l_Lean_Grind_grindLintInspect);
l_Lean_Grind_grindLintMute___closed__0 = _init_l_Lean_Grind_grindLintMute___closed__0();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__0);
l_Lean_Grind_grindLintMute___closed__1 = _init_l_Lean_Grind_grindLintMute___closed__1();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__1);
l_Lean_Grind_grindLintMute___closed__2 = _init_l_Lean_Grind_grindLintMute___closed__2();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__2);
l_Lean_Grind_grindLintMute___closed__3 = _init_l_Lean_Grind_grindLintMute___closed__3();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__3);
l_Lean_Grind_grindLintMute___closed__4 = _init_l_Lean_Grind_grindLintMute___closed__4();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__4);
l_Lean_Grind_grindLintMute___closed__5 = _init_l_Lean_Grind_grindLintMute___closed__5();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__5);
l_Lean_Grind_grindLintMute___closed__6 = _init_l_Lean_Grind_grindLintMute___closed__6();
lean_mark_persistent(l_Lean_Grind_grindLintMute___closed__6);
l_Lean_Grind_grindLintMute = _init_l_Lean_Grind_grindLintMute();
lean_mark_persistent(l_Lean_Grind_grindLintMute);
l_Lean_Grind_grindLintSkip___closed__0 = _init_l_Lean_Grind_grindLintSkip___closed__0();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__0);
l_Lean_Grind_grindLintSkip___closed__1 = _init_l_Lean_Grind_grindLintSkip___closed__1();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__1);
l_Lean_Grind_grindLintSkip___closed__2 = _init_l_Lean_Grind_grindLintSkip___closed__2();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__2);
l_Lean_Grind_grindLintSkip___closed__3 = _init_l_Lean_Grind_grindLintSkip___closed__3();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__3);
l_Lean_Grind_grindLintSkip___closed__4 = _init_l_Lean_Grind_grindLintSkip___closed__4();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__4);
l_Lean_Grind_grindLintSkip___closed__5 = _init_l_Lean_Grind_grindLintSkip___closed__5();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__5);
l_Lean_Grind_grindLintSkip___closed__6 = _init_l_Lean_Grind_grindLintSkip___closed__6();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__6);
l_Lean_Grind_grindLintSkip___closed__7 = _init_l_Lean_Grind_grindLintSkip___closed__7();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__7);
l_Lean_Grind_grindLintSkip___closed__8 = _init_l_Lean_Grind_grindLintSkip___closed__8();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__8);
l_Lean_Grind_grindLintSkip___closed__9 = _init_l_Lean_Grind_grindLintSkip___closed__9();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__9);
l_Lean_Grind_grindLintSkip___closed__10 = _init_l_Lean_Grind_grindLintSkip___closed__10();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__10);
l_Lean_Grind_grindLintSkip___closed__11 = _init_l_Lean_Grind_grindLintSkip___closed__11();
lean_mark_persistent(l_Lean_Grind_grindLintSkip___closed__11);
l_Lean_Grind_grindLintSkip = _init_l_Lean_Grind_grindLintSkip();
lean_mark_persistent(l_Lean_Grind_grindLintSkip);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
