// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: Init.Tactics
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
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__12;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__7;
static lean_object* l_Lean_Parser_Tactic_grind___closed__11;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__6;
static lean_object* l_Lean_Parser_Attr_grindUsr___closed__5;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__4;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__15;
static lean_object* l_Lean_Parser_Tactic_grind___closed__7;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__5;
static lean_object* l_Lean_Parser_Tactic_grind___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindUsr;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__2;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__15;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindBwd;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__6;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__5;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__18;
static lean_object* l_Lean_Parser_Tactic_grind___closed__24;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__6;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__2;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__1;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__4;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__10;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__5;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__1;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__8;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__4;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__6;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__5;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__6;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__9;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindFwd;
static lean_object* l_Lean_Parser_Tactic_grind___closed__29;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__2;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__11;
static lean_object* l_Lean_Parser_Attr_grindUsr___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__8;
static lean_object* l_Lean_Parser_Tactic_grind___closed__23;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEqBwd;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__4;
static lean_object* l_Lean_Parser_Attr_grindEq___closed__3;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__16;
static lean_object* l_Lean_Parser_Attr_grind___closed__4;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__2;
static lean_object* l_Lean_Grind_instInhabitedConfig___closed__1;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEq___closed__4;
static lean_object* l_Lean_Parser_Attr_grindEqRhs___closed__4;
static lean_object* l_Lean_Parser_Tactic_grind___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEqRhs;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindCasesEager;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__5;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindIntro___closed__2;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__8;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__8;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__4;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__9;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindParam;
static lean_object* l_Lean_Parser_Attr_grindCases___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grind;
static lean_object* l_Lean_Parser_Attr_grindEq___closed__5;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__9;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__2;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__9;
static lean_object* l_Lean_Parser_Attr_grindEqRhs___closed__1;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__12;
static lean_object* l_Lean_Parser_Tactic_grind___closed__6;
static lean_object* l_Lean_Parser_Attr_grindIntro___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEq___closed__1;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grind;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__13;
static lean_object* l_Lean_Parser_Tactic_grind___closed__14;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__2;
static lean_object* l_Lean_Grind_instBEqConfig___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__8;
static lean_object* l_Lean_Parser_Tactic_grind___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__7;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__2;
static lean_object* l_Lean_Parser_Tactic_grind___closed__9;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__8;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__13;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__1;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__3;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__5;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindTrace;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__7;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindMod;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindErase;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__9;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__12;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__1;
static lean_object* l_Lean_Parser_Tactic_grind___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEqBoth;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__14;
static lean_object* l_Lean_Parser_Attr_grindIntro___closed__5;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindLemma;
LEAN_EXPORT lean_object* l_Lean_Grind_instInhabitedConfig;
static lean_object* l_Lean_Parser_Attr_grindUsr___closed__4;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__3;
static lean_object* l_Lean_Parser_Attr_grind___closed__3;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindIntro;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__9;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__7;
static lean_object* l_Lean_Parser_Attr_grindCases___closed__4;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__7;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__10;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__13;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__1;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_376_(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_grind___closed__17;
static lean_object* l_Lean_Parser_Tactic_grind___closed__5;
static lean_object* l_Lean_Parser_Tactic_grind___closed__18;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__1;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__1;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_resetGrindAttrs;
static lean_object* l_Lean_Parser_Attr_grindCases___closed__2;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__5;
static lean_object* l_Lean_Parser_Attr_grind___closed__2;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__8;
static lean_object* l_Lean_Parser_Attr_grindUsr___closed__3;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__7;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__3;
static lean_object* l_Lean_Parser_Tactic_grind___closed__13;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__12;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__12;
static lean_object* l_Lean_Parser_Attr_grindEqRhs___closed__5;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindCases;
static lean_object* l_Lean_Parser_Tactic_grind___closed__3;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindLR;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__10;
static lean_object* l_Lean_Parser_Attr_grind___closed__6;
static lean_object* l_Lean_Parser_Attr_grindIntro___closed__3;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__8;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__9;
static lean_object* l_Lean_Parser_Attr_grindCases___closed__3;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__6;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__9;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__8;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__4;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__1;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindRL___closed__12;
static lean_object* l_Lean_Parser_Tactic_grind___closed__27;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__11;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__10;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__3;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__11;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__14;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__4;
static lean_object* l_Lean_Parser_Attr_grindUsr___closed__2;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__7;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__3;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__2;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__3;
static lean_object* l_Lean_Parser_Tactic_grind___closed__25;
static lean_object* l_Lean_Parser_Tactic_grind___closed__19;
static lean_object* l_Lean_Parser_Attr_grindEqRhs___closed__3;
static lean_object* l_Lean_Parser_Attr_grindCases___closed__1;
static lean_object* l_Lean_Parser_Attr_grindEq___closed__2;
static lean_object* l_Lean_Parser_Attr_grindEq___closed__6;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__17;
static lean_object* l_Lean_Parser_Tactic_grind___closed__28;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__2;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__7;
static lean_object* l_Lean_Parser_Attr_grindRL___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEq;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindRL;
static lean_object* l_Lean_Parser_Tactic_grind___closed__26;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__1;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__5;
static lean_object* l_Lean_Parser_Tactic_grind___closed__4;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__11;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__9;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__7;
static lean_object* l_Lean_Parser_Attr_grind___closed__5;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__10;
static lean_object* l_Lean_Parser_Tactic_grind___closed__30;
static lean_object* l_Lean_Parser_Tactic_grind___closed__21;
static lean_object* l_Lean_Parser_Tactic_grind___closed__8;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__14;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__10;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__5;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__3;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__2;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__8;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__9;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__13;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__1;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__4;
static lean_object* l_Lean_Parser_Attr_grindLR___closed__12;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__16;
static lean_object* l_Lean_Parser_Attr_grind___closed__8;
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__4;
static lean_object* l_Lean_Parser_Attr_grindCasesEager___closed__4;
static lean_object* l_Lean_Parser_Attr_grind___closed__7;
static lean_object* l_Lean_Parser_Tactic_grind___closed__20;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__6;
static lean_object* l_Lean_Parser_Attr_grindEqBwd___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_376____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__5;
static lean_object* l_Lean_Parser_Attr_grindFwd___closed__2;
static lean_object* l_Lean_Parser_Tactic_grindErase___closed__10;
static lean_object* l_Lean_Parser_Attr_grindEqRhs___closed__2;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__3;
static lean_object* l_Lean_Parser_Attr_grind___closed__1;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__3;
static lean_object* l_Lean_Parser_Tactic_grind___closed__22;
static lean_object* l_Lean_Parser_Attr_grindIntro___closed__4;
static lean_object* l_Lean_Parser_resetGrindAttrs___closed__2;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__3;
static lean_object* l_Lean_Parser_Tactic_grind___closed__16;
static lean_object* l_Lean_Parser_Tactic_grind___closed__12;
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resetGrindAttrs", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_resetGrindAttrs___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reset_grind_attrs%", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__4;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_resetGrindAttrs___closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_resetGrindAttrs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindEq___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("= ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindEq___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEq___closed__2;
x_2 = l_Lean_Parser_Attr_grindEq___closed__3;
x_3 = l_Lean_Parser_Attr_grindEq___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindEq___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindEqBoth___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("atomic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__9;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__8;
x_3 = l_Lean_Parser_Attr_grindEqBoth___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__11;
x_3 = l_Lean_Parser_Attr_grindEqBoth___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__1;
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__2;
x_3 = l_Lean_Parser_Attr_grindEqBoth___closed__15;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__16;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindEqRhs___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBoth___closed__10;
x_3 = l_Lean_Parser_Attr_grindEqBoth___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqRhs___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqRhs___closed__1;
x_2 = l_Lean_Parser_Attr_grindEqRhs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEqRhs___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindEqRhs___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindEqBwd___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("←", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__8;
x_3 = l_Lean_Parser_Attr_grindEq___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<-", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__13;
x_3 = l_Lean_Parser_Attr_grindEq___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__6;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__11;
x_3 = l_Lean_Parser_Attr_grindEqBwd___closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__1;
x_2 = l_Lean_Parser_Attr_grindEqBwd___closed__2;
x_3 = l_Lean_Parser_Attr_grindEqBwd___closed__17;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__18;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindBwd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindBwd___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindBwd___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindBwd___closed__5;
x_3 = l_Lean_Parser_Attr_grindBwd___closed__6;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindBwd___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__8;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__8;
x_2 = l_Lean_Parser_Attr_grindBwd___closed__9;
x_3 = l_Lean_Parser_Attr_grindBwd___closed__10;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindBwd___closed__7;
x_3 = l_Lean_Parser_Attr_grindBwd___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__1;
x_2 = l_Lean_Parser_Attr_grindBwd___closed__2;
x_3 = l_Lean_Parser_Attr_grindBwd___closed__12;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__13;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindFwd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindFwd___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("→ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindFwd___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindFwd___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindFwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindFwd___closed__4;
x_3 = l_Lean_Parser_Attr_grindFwd___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<- ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindFwd___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindFwd___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindFwd___closed__7;
x_2 = l_Lean_Parser_Attr_grindFwd___closed__8;
x_3 = l_Lean_Parser_Attr_grindFwd___closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindFwd___closed__6;
x_3 = l_Lean_Parser_Attr_grindFwd___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindFwd___closed__1;
x_2 = l_Lean_Parser_Attr_grindFwd___closed__2;
x_3 = l_Lean_Parser_Attr_grindFwd___closed__11;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindFwd___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindRL", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindRL___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⇐ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindRL___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindRL___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindRL___closed__3;
x_2 = l_Lean_Parser_Attr_grindRL___closed__4;
x_3 = l_Lean_Parser_Attr_grindRL___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<= ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindRL___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindRL___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindRL___closed__7;
x_2 = l_Lean_Parser_Attr_grindRL___closed__8;
x_3 = l_Lean_Parser_Attr_grindRL___closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindRL___closed__6;
x_3 = l_Lean_Parser_Attr_grindRL___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindRL___closed__1;
x_2 = l_Lean_Parser_Attr_grindRL___closed__2;
x_3 = l_Lean_Parser_Attr_grindRL___closed__11;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindRL___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLR", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindLR___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⇒ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindLR___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindLR___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindLR___closed__3;
x_2 = l_Lean_Parser_Attr_grindLR___closed__4;
x_3 = l_Lean_Parser_Attr_grindLR___closed__5;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindBwd___closed__3;
x_2 = l_Lean_Parser_Attr_grindLR___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Attr_grindLR___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindLR___closed__7;
x_2 = l_Lean_Parser_Attr_grindLR___closed__8;
x_3 = l_Lean_Parser_Attr_grindLR___closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindLR___closed__6;
x_3 = l_Lean_Parser_Attr_grindLR___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindLR___closed__1;
x_2 = l_Lean_Parser_Attr_grindLR___closed__2;
x_3 = l_Lean_Parser_Attr_grindLR___closed__11;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindLR___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindUsr", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindUsr___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("usr ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindUsr___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindUsr___closed__1;
x_2 = l_Lean_Parser_Attr_grindUsr___closed__2;
x_3 = l_Lean_Parser_Attr_grindUsr___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindUsr___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindCases", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindCases___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindCases___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindCases___closed__1;
x_2 = l_Lean_Parser_Attr_grindCases___closed__2;
x_3 = l_Lean_Parser_Attr_grindCases___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindCases___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindCasesEager___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindCasesEager___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eager ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindCasesEager___closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grindCasesEager___closed__4;
x_3 = l_Lean_Parser_Attr_grindCasesEager___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__4;
x_2 = l_Lean_Parser_Attr_grindCasesEager___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindCasesEager___closed__1;
x_2 = l_Lean_Parser_Attr_grindCasesEager___closed__2;
x_3 = l_Lean_Parser_Attr_grindCasesEager___closed__8;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindCasesEager___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindIntro", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindIntro___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindIntro___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindIntro___closed__1;
x_2 = l_Lean_Parser_Attr_grindIntro___closed__2;
x_3 = l_Lean_Parser_Attr_grindIntro___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindIntro___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindMod", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindMod___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindCases;
x_3 = l_Lean_Parser_Attr_grindIntro;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindCasesEager;
x_3 = l_Lean_Parser_Attr_grindMod___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindUsr;
x_3 = l_Lean_Parser_Attr_grindMod___closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindLR;
x_3 = l_Lean_Parser_Attr_grindMod___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindRL;
x_3 = l_Lean_Parser_Attr_grindMod___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindFwd;
x_3 = l_Lean_Parser_Attr_grindMod___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindBwd;
x_3 = l_Lean_Parser_Attr_grindMod___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBwd;
x_3 = l_Lean_Parser_Attr_grindMod___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindEq;
x_3 = l_Lean_Parser_Attr_grindMod___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqRhs;
x_3 = l_Lean_Parser_Attr_grindMod___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBoth;
x_3 = l_Lean_Parser_Attr_grindMod___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindMod___closed__1;
x_2 = l_Lean_Parser_Attr_grindMod___closed__2;
x_3 = l_Lean_Parser_Attr_grindMod___closed__13;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindMod___closed__14;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grind___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grind___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optional", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Attr_grind___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grind___closed__5;
x_2 = l_Lean_Parser_Attr_grindMod;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grind___closed__3;
x_3 = l_Lean_Parser_Attr_grind___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grind___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Attr_grind___closed__7;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grind___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedConfig___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 6, 13);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 3, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 4, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 5, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 6, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 7, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 8, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 9, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 10, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 11, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 12, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instInhabitedConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_376_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_46; uint8_t x_53; uint8_t x_60; uint8_t x_67; uint8_t x_74; uint8_t x_81; uint8_t x_92; uint8_t x_99; uint8_t x_106; uint8_t x_113; uint8_t x_120; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 4);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 5);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 7);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 8);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 9);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 10);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 11);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 12);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 2);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 3);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 4);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 5);
x_32 = lean_ctor_get(x_2, 4);
x_33 = lean_ctor_get(x_2, 5);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 6);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 7);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 8);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 9);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 10);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 11);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 12);
if (x_3 == 0)
{
if (x_22 == 0)
{
uint8_t x_135; 
x_135 = 1;
x_120 = x_135;
goto block_134;
}
else
{
uint8_t x_136; 
x_136 = 0;
x_120 = x_136;
goto block_134;
}
}
else
{
if (x_22 == 0)
{
uint8_t x_137; 
x_137 = 0;
x_120 = x_137;
goto block_134;
}
else
{
uint8_t x_138; 
x_138 = 1;
x_120 = x_138;
goto block_134;
}
}
block_45:
{
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
else
{
if (x_21 == 0)
{
if (x_40 == 0)
{
uint8_t x_43; 
x_43 = 1;
return x_43;
}
else
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
}
else
{
return x_40;
}
}
}
block_52:
{
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = 0;
return x_47;
}
else
{
if (x_20 == 0)
{
if (x_39 == 0)
{
uint8_t x_48; 
x_48 = 1;
x_41 = x_48;
goto block_45;
}
else
{
uint8_t x_49; 
x_49 = 0;
x_41 = x_49;
goto block_45;
}
}
else
{
if (x_39 == 0)
{
uint8_t x_50; 
x_50 = 0;
x_41 = x_50;
goto block_45;
}
else
{
uint8_t x_51; 
x_51 = 1;
x_41 = x_51;
goto block_45;
}
}
}
}
block_59:
{
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = 0;
return x_54;
}
else
{
if (x_19 == 0)
{
if (x_38 == 0)
{
uint8_t x_55; 
x_55 = 1;
x_46 = x_55;
goto block_52;
}
else
{
uint8_t x_56; 
x_56 = 0;
x_46 = x_56;
goto block_52;
}
}
else
{
if (x_38 == 0)
{
uint8_t x_57; 
x_57 = 0;
x_46 = x_57;
goto block_52;
}
else
{
uint8_t x_58; 
x_58 = 1;
x_46 = x_58;
goto block_52;
}
}
}
}
block_66:
{
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = 0;
return x_61;
}
else
{
if (x_18 == 0)
{
if (x_37 == 0)
{
uint8_t x_62; 
x_62 = 1;
x_53 = x_62;
goto block_59;
}
else
{
uint8_t x_63; 
x_63 = 0;
x_53 = x_63;
goto block_59;
}
}
else
{
if (x_37 == 0)
{
uint8_t x_64; 
x_64 = 0;
x_53 = x_64;
goto block_59;
}
else
{
uint8_t x_65; 
x_65 = 1;
x_53 = x_65;
goto block_59;
}
}
}
}
block_73:
{
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = 0;
return x_68;
}
else
{
if (x_17 == 0)
{
if (x_36 == 0)
{
uint8_t x_69; 
x_69 = 1;
x_60 = x_69;
goto block_66;
}
else
{
uint8_t x_70; 
x_70 = 0;
x_60 = x_70;
goto block_66;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_71; 
x_71 = 0;
x_60 = x_71;
goto block_66;
}
else
{
uint8_t x_72; 
x_72 = 1;
x_60 = x_72;
goto block_66;
}
}
}
}
block_80:
{
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = 0;
return x_75;
}
else
{
if (x_16 == 0)
{
if (x_35 == 0)
{
uint8_t x_76; 
x_76 = 1;
x_67 = x_76;
goto block_73;
}
else
{
uint8_t x_77; 
x_77 = 0;
x_67 = x_77;
goto block_73;
}
}
else
{
if (x_35 == 0)
{
uint8_t x_78; 
x_78 = 0;
x_67 = x_78;
goto block_73;
}
else
{
uint8_t x_79; 
x_79 = 1;
x_67 = x_79;
goto block_73;
}
}
}
}
block_91:
{
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = 0;
return x_82;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_eq(x_13, x_32);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = 0;
return x_84;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_eq(x_14, x_33);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = 0;
return x_86;
}
else
{
if (x_15 == 0)
{
if (x_34 == 0)
{
uint8_t x_87; 
x_87 = 1;
x_74 = x_87;
goto block_80;
}
else
{
uint8_t x_88; 
x_88 = 0;
x_74 = x_88;
goto block_80;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_89; 
x_89 = 0;
x_74 = x_89;
goto block_80;
}
else
{
uint8_t x_90; 
x_90 = 1;
x_74 = x_90;
goto block_80;
}
}
}
}
}
}
block_98:
{
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
return x_93;
}
else
{
if (x_12 == 0)
{
if (x_31 == 0)
{
uint8_t x_94; 
x_94 = 1;
x_81 = x_94;
goto block_91;
}
else
{
uint8_t x_95; 
x_95 = 0;
x_81 = x_95;
goto block_91;
}
}
else
{
if (x_31 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_81 = x_96;
goto block_91;
}
else
{
uint8_t x_97; 
x_97 = 1;
x_81 = x_97;
goto block_91;
}
}
}
}
block_105:
{
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = 0;
return x_100;
}
else
{
if (x_11 == 0)
{
if (x_30 == 0)
{
uint8_t x_101; 
x_101 = 1;
x_92 = x_101;
goto block_98;
}
else
{
uint8_t x_102; 
x_102 = 0;
x_92 = x_102;
goto block_98;
}
}
else
{
if (x_30 == 0)
{
uint8_t x_103; 
x_103 = 0;
x_92 = x_103;
goto block_98;
}
else
{
uint8_t x_104; 
x_104 = 1;
x_92 = x_104;
goto block_98;
}
}
}
}
block_112:
{
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = 0;
return x_107;
}
else
{
if (x_10 == 0)
{
if (x_29 == 0)
{
uint8_t x_108; 
x_108 = 1;
x_99 = x_108;
goto block_105;
}
else
{
uint8_t x_109; 
x_109 = 0;
x_99 = x_109;
goto block_105;
}
}
else
{
if (x_29 == 0)
{
uint8_t x_110; 
x_110 = 0;
x_99 = x_110;
goto block_105;
}
else
{
uint8_t x_111; 
x_111 = 1;
x_99 = x_111;
goto block_105;
}
}
}
}
block_119:
{
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = 0;
return x_114;
}
else
{
if (x_9 == 0)
{
if (x_28 == 0)
{
uint8_t x_115; 
x_115 = 1;
x_106 = x_115;
goto block_112;
}
else
{
uint8_t x_116; 
x_116 = 0;
x_106 = x_116;
goto block_112;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_117; 
x_117 = 0;
x_106 = x_117;
goto block_112;
}
else
{
uint8_t x_118; 
x_118 = 1;
x_106 = x_118;
goto block_112;
}
}
}
}
block_134:
{
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = 0;
return x_121;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_eq(x_4, x_23);
if (x_122 == 0)
{
uint8_t x_123; 
x_123 = 0;
return x_123;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_eq(x_5, x_24);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = 0;
return x_125;
}
else
{
uint8_t x_126; 
x_126 = lean_nat_dec_eq(x_6, x_25);
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = 0;
return x_127;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_eq(x_7, x_26);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = 0;
return x_129;
}
else
{
if (x_8 == 0)
{
if (x_27 == 0)
{
uint8_t x_130; 
x_130 = 1;
x_113 = x_130;
goto block_119;
}
else
{
uint8_t x_131; 
x_131 = 0;
x_113 = x_131;
goto block_119;
}
}
else
{
if (x_27 == 0)
{
uint8_t x_132; 
x_132 = 0;
x_113 = x_132;
goto block_119;
}
else
{
uint8_t x_133; 
x_133 = 1;
x_113 = x_133;
goto block_119;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_376____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_376_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_instBEqConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_376____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instBEqConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindErase", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__1;
x_4 = l_Lean_Parser_Tactic_grindErase___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_grindErase___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_grindErase___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_grindErase___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grindErase___closed__5;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_grindErase___closed__2;
x_2 = l_Lean_Parser_Tactic_grindErase___closed__3;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_grindErase___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLemma", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__1;
x_4 = l_Lean_Parser_Tactic_grindLemma___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grind___closed__6;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_grindLemma___closed__1;
x_2 = l_Lean_Parser_Tactic_grindLemma___closed__2;
x_3 = l_Lean_Parser_Tactic_grindLemma___closed__3;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_grindLemma___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindParam", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__1;
x_4 = l_Lean_Parser_Tactic_grindParam___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Tactic_grindErase;
x_3 = l_Lean_Parser_Tactic_grindLemma;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_grindParam___closed__1;
x_2 = l_Lean_Parser_Tactic_grindParam___closed__2;
x_3 = l_Lean_Parser_Tactic_grindParam___closed__3;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_grindParam___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__1;
x_4 = l_Lean_Parser_Attr_grind___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Attr_grind___closed__3;
x_3 = l_Lean_Parser_Tactic_optConfig;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" only", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_grind___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grind___closed__5;
x_2 = l_Lean_Parser_Tactic_grind___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grind___closed__2;
x_3 = l_Lean_Parser_Tactic_grind___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" [", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_grind___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withoutPosition", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_grind___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_grind___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_grindParam;
x_2 = l_Lean_Parser_Tactic_grind___closed__13;
x_3 = l_Lean_Parser_Tactic_grind___closed__12;
x_4 = 0;
x_5 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_grind___closed__10;
x_2 = l_Lean_Parser_Tactic_grind___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grind___closed__8;
x_3 = l_Lean_Parser_Tactic_grind___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_grind___closed__17;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grind___closed__16;
x_3 = l_Lean_Parser_Tactic_grind___closed__18;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grind___closed__5;
x_2 = l_Lean_Parser_Tactic_grind___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grind___closed__6;
x_3 = l_Lean_Parser_Tactic_grind___closed__20;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("on_failure ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_grind___closed__22;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_grind___closed__24;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_grind___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grind___closed__23;
x_3 = l_Lean_Parser_Tactic_grind___closed__26;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grind___closed__5;
x_2 = l_Lean_Parser_Tactic_grind___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grind___closed__21;
x_3 = l_Lean_Parser_Tactic_grind___closed__28;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_grind___closed__1;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_grind___closed__29;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_grind___closed__30;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindTrace", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Tactic_grindErase___closed__1;
x_4 = l_Lean_Parser_Tactic_grindTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind\?", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_grindTrace___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grindTrace___closed__4;
x_3 = l_Lean_Parser_Tactic_optConfig;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grindTrace___closed__5;
x_3 = l_Lean_Parser_Tactic_grind___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grindTrace___closed__6;
x_3 = l_Lean_Parser_Tactic_grind___closed__20;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindEqBoth___closed__6;
x_2 = l_Lean_Parser_Tactic_grindTrace___closed__7;
x_3 = l_Lean_Parser_Tactic_grind___closed__28;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_grindTrace___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_grindTrace___closed__8;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_grindTrace___closed__9;
return x_1;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_resetGrindAttrs___closed__1 = _init_l_Lean_Parser_resetGrindAttrs___closed__1();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__1);
l_Lean_Parser_resetGrindAttrs___closed__2 = _init_l_Lean_Parser_resetGrindAttrs___closed__2();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__2);
l_Lean_Parser_resetGrindAttrs___closed__3 = _init_l_Lean_Parser_resetGrindAttrs___closed__3();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__3);
l_Lean_Parser_resetGrindAttrs___closed__4 = _init_l_Lean_Parser_resetGrindAttrs___closed__4();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__4);
l_Lean_Parser_resetGrindAttrs___closed__5 = _init_l_Lean_Parser_resetGrindAttrs___closed__5();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__5);
l_Lean_Parser_resetGrindAttrs___closed__6 = _init_l_Lean_Parser_resetGrindAttrs___closed__6();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__6);
l_Lean_Parser_resetGrindAttrs___closed__7 = _init_l_Lean_Parser_resetGrindAttrs___closed__7();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs___closed__7);
l_Lean_Parser_resetGrindAttrs = _init_l_Lean_Parser_resetGrindAttrs();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs);
l_Lean_Parser_Attr_grindEq___closed__1 = _init_l_Lean_Parser_Attr_grindEq___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq___closed__1);
l_Lean_Parser_Attr_grindEq___closed__2 = _init_l_Lean_Parser_Attr_grindEq___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq___closed__2);
l_Lean_Parser_Attr_grindEq___closed__3 = _init_l_Lean_Parser_Attr_grindEq___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq___closed__3);
l_Lean_Parser_Attr_grindEq___closed__4 = _init_l_Lean_Parser_Attr_grindEq___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq___closed__4);
l_Lean_Parser_Attr_grindEq___closed__5 = _init_l_Lean_Parser_Attr_grindEq___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq___closed__5);
l_Lean_Parser_Attr_grindEq___closed__6 = _init_l_Lean_Parser_Attr_grindEq___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq___closed__6);
l_Lean_Parser_Attr_grindEq = _init_l_Lean_Parser_Attr_grindEq();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq);
l_Lean_Parser_Attr_grindEqBoth___closed__1 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__1);
l_Lean_Parser_Attr_grindEqBoth___closed__2 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__2);
l_Lean_Parser_Attr_grindEqBoth___closed__3 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__3);
l_Lean_Parser_Attr_grindEqBoth___closed__4 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__4);
l_Lean_Parser_Attr_grindEqBoth___closed__5 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__5);
l_Lean_Parser_Attr_grindEqBoth___closed__6 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__6);
l_Lean_Parser_Attr_grindEqBoth___closed__7 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__7);
l_Lean_Parser_Attr_grindEqBoth___closed__8 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__8);
l_Lean_Parser_Attr_grindEqBoth___closed__9 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__9);
l_Lean_Parser_Attr_grindEqBoth___closed__10 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__10);
l_Lean_Parser_Attr_grindEqBoth___closed__11 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__11);
l_Lean_Parser_Attr_grindEqBoth___closed__12 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__12);
l_Lean_Parser_Attr_grindEqBoth___closed__13 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__13();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__13);
l_Lean_Parser_Attr_grindEqBoth___closed__14 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__14();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__14);
l_Lean_Parser_Attr_grindEqBoth___closed__15 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__15();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__15);
l_Lean_Parser_Attr_grindEqBoth___closed__16 = _init_l_Lean_Parser_Attr_grindEqBoth___closed__16();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth___closed__16);
l_Lean_Parser_Attr_grindEqBoth = _init_l_Lean_Parser_Attr_grindEqBoth();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth);
l_Lean_Parser_Attr_grindEqRhs___closed__1 = _init_l_Lean_Parser_Attr_grindEqRhs___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs___closed__1);
l_Lean_Parser_Attr_grindEqRhs___closed__2 = _init_l_Lean_Parser_Attr_grindEqRhs___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs___closed__2);
l_Lean_Parser_Attr_grindEqRhs___closed__3 = _init_l_Lean_Parser_Attr_grindEqRhs___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs___closed__3);
l_Lean_Parser_Attr_grindEqRhs___closed__4 = _init_l_Lean_Parser_Attr_grindEqRhs___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs___closed__4);
l_Lean_Parser_Attr_grindEqRhs___closed__5 = _init_l_Lean_Parser_Attr_grindEqRhs___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs___closed__5);
l_Lean_Parser_Attr_grindEqRhs = _init_l_Lean_Parser_Attr_grindEqRhs();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs);
l_Lean_Parser_Attr_grindEqBwd___closed__1 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__1);
l_Lean_Parser_Attr_grindEqBwd___closed__2 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__2);
l_Lean_Parser_Attr_grindEqBwd___closed__3 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__3);
l_Lean_Parser_Attr_grindEqBwd___closed__4 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__4);
l_Lean_Parser_Attr_grindEqBwd___closed__5 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__5);
l_Lean_Parser_Attr_grindEqBwd___closed__6 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__6);
l_Lean_Parser_Attr_grindEqBwd___closed__7 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__7);
l_Lean_Parser_Attr_grindEqBwd___closed__8 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__8);
l_Lean_Parser_Attr_grindEqBwd___closed__9 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__9);
l_Lean_Parser_Attr_grindEqBwd___closed__10 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__10);
l_Lean_Parser_Attr_grindEqBwd___closed__11 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__11);
l_Lean_Parser_Attr_grindEqBwd___closed__12 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__12);
l_Lean_Parser_Attr_grindEqBwd___closed__13 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__13();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__13);
l_Lean_Parser_Attr_grindEqBwd___closed__14 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__14();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__14);
l_Lean_Parser_Attr_grindEqBwd___closed__15 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__15();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__15);
l_Lean_Parser_Attr_grindEqBwd___closed__16 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__16();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__16);
l_Lean_Parser_Attr_grindEqBwd___closed__17 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__17();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__17);
l_Lean_Parser_Attr_grindEqBwd___closed__18 = _init_l_Lean_Parser_Attr_grindEqBwd___closed__18();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd___closed__18);
l_Lean_Parser_Attr_grindEqBwd = _init_l_Lean_Parser_Attr_grindEqBwd();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd);
l_Lean_Parser_Attr_grindBwd___closed__1 = _init_l_Lean_Parser_Attr_grindBwd___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__1);
l_Lean_Parser_Attr_grindBwd___closed__2 = _init_l_Lean_Parser_Attr_grindBwd___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__2);
l_Lean_Parser_Attr_grindBwd___closed__3 = _init_l_Lean_Parser_Attr_grindBwd___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__3);
l_Lean_Parser_Attr_grindBwd___closed__4 = _init_l_Lean_Parser_Attr_grindBwd___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__4);
l_Lean_Parser_Attr_grindBwd___closed__5 = _init_l_Lean_Parser_Attr_grindBwd___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__5);
l_Lean_Parser_Attr_grindBwd___closed__6 = _init_l_Lean_Parser_Attr_grindBwd___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__6);
l_Lean_Parser_Attr_grindBwd___closed__7 = _init_l_Lean_Parser_Attr_grindBwd___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__7);
l_Lean_Parser_Attr_grindBwd___closed__8 = _init_l_Lean_Parser_Attr_grindBwd___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__8);
l_Lean_Parser_Attr_grindBwd___closed__9 = _init_l_Lean_Parser_Attr_grindBwd___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__9);
l_Lean_Parser_Attr_grindBwd___closed__10 = _init_l_Lean_Parser_Attr_grindBwd___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__10);
l_Lean_Parser_Attr_grindBwd___closed__11 = _init_l_Lean_Parser_Attr_grindBwd___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__11);
l_Lean_Parser_Attr_grindBwd___closed__12 = _init_l_Lean_Parser_Attr_grindBwd___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__12);
l_Lean_Parser_Attr_grindBwd___closed__13 = _init_l_Lean_Parser_Attr_grindBwd___closed__13();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd___closed__13);
l_Lean_Parser_Attr_grindBwd = _init_l_Lean_Parser_Attr_grindBwd();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd);
l_Lean_Parser_Attr_grindFwd___closed__1 = _init_l_Lean_Parser_Attr_grindFwd___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__1);
l_Lean_Parser_Attr_grindFwd___closed__2 = _init_l_Lean_Parser_Attr_grindFwd___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__2);
l_Lean_Parser_Attr_grindFwd___closed__3 = _init_l_Lean_Parser_Attr_grindFwd___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__3);
l_Lean_Parser_Attr_grindFwd___closed__4 = _init_l_Lean_Parser_Attr_grindFwd___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__4);
l_Lean_Parser_Attr_grindFwd___closed__5 = _init_l_Lean_Parser_Attr_grindFwd___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__5);
l_Lean_Parser_Attr_grindFwd___closed__6 = _init_l_Lean_Parser_Attr_grindFwd___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__6);
l_Lean_Parser_Attr_grindFwd___closed__7 = _init_l_Lean_Parser_Attr_grindFwd___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__7);
l_Lean_Parser_Attr_grindFwd___closed__8 = _init_l_Lean_Parser_Attr_grindFwd___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__8);
l_Lean_Parser_Attr_grindFwd___closed__9 = _init_l_Lean_Parser_Attr_grindFwd___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__9);
l_Lean_Parser_Attr_grindFwd___closed__10 = _init_l_Lean_Parser_Attr_grindFwd___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__10);
l_Lean_Parser_Attr_grindFwd___closed__11 = _init_l_Lean_Parser_Attr_grindFwd___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__11);
l_Lean_Parser_Attr_grindFwd___closed__12 = _init_l_Lean_Parser_Attr_grindFwd___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd___closed__12);
l_Lean_Parser_Attr_grindFwd = _init_l_Lean_Parser_Attr_grindFwd();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd);
l_Lean_Parser_Attr_grindRL___closed__1 = _init_l_Lean_Parser_Attr_grindRL___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__1);
l_Lean_Parser_Attr_grindRL___closed__2 = _init_l_Lean_Parser_Attr_grindRL___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__2);
l_Lean_Parser_Attr_grindRL___closed__3 = _init_l_Lean_Parser_Attr_grindRL___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__3);
l_Lean_Parser_Attr_grindRL___closed__4 = _init_l_Lean_Parser_Attr_grindRL___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__4);
l_Lean_Parser_Attr_grindRL___closed__5 = _init_l_Lean_Parser_Attr_grindRL___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__5);
l_Lean_Parser_Attr_grindRL___closed__6 = _init_l_Lean_Parser_Attr_grindRL___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__6);
l_Lean_Parser_Attr_grindRL___closed__7 = _init_l_Lean_Parser_Attr_grindRL___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__7);
l_Lean_Parser_Attr_grindRL___closed__8 = _init_l_Lean_Parser_Attr_grindRL___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__8);
l_Lean_Parser_Attr_grindRL___closed__9 = _init_l_Lean_Parser_Attr_grindRL___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__9);
l_Lean_Parser_Attr_grindRL___closed__10 = _init_l_Lean_Parser_Attr_grindRL___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__10);
l_Lean_Parser_Attr_grindRL___closed__11 = _init_l_Lean_Parser_Attr_grindRL___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__11);
l_Lean_Parser_Attr_grindRL___closed__12 = _init_l_Lean_Parser_Attr_grindRL___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL___closed__12);
l_Lean_Parser_Attr_grindRL = _init_l_Lean_Parser_Attr_grindRL();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL);
l_Lean_Parser_Attr_grindLR___closed__1 = _init_l_Lean_Parser_Attr_grindLR___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__1);
l_Lean_Parser_Attr_grindLR___closed__2 = _init_l_Lean_Parser_Attr_grindLR___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__2);
l_Lean_Parser_Attr_grindLR___closed__3 = _init_l_Lean_Parser_Attr_grindLR___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__3);
l_Lean_Parser_Attr_grindLR___closed__4 = _init_l_Lean_Parser_Attr_grindLR___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__4);
l_Lean_Parser_Attr_grindLR___closed__5 = _init_l_Lean_Parser_Attr_grindLR___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__5);
l_Lean_Parser_Attr_grindLR___closed__6 = _init_l_Lean_Parser_Attr_grindLR___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__6);
l_Lean_Parser_Attr_grindLR___closed__7 = _init_l_Lean_Parser_Attr_grindLR___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__7);
l_Lean_Parser_Attr_grindLR___closed__8 = _init_l_Lean_Parser_Attr_grindLR___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__8);
l_Lean_Parser_Attr_grindLR___closed__9 = _init_l_Lean_Parser_Attr_grindLR___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__9);
l_Lean_Parser_Attr_grindLR___closed__10 = _init_l_Lean_Parser_Attr_grindLR___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__10);
l_Lean_Parser_Attr_grindLR___closed__11 = _init_l_Lean_Parser_Attr_grindLR___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__11);
l_Lean_Parser_Attr_grindLR___closed__12 = _init_l_Lean_Parser_Attr_grindLR___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR___closed__12);
l_Lean_Parser_Attr_grindLR = _init_l_Lean_Parser_Attr_grindLR();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR);
l_Lean_Parser_Attr_grindUsr___closed__1 = _init_l_Lean_Parser_Attr_grindUsr___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr___closed__1);
l_Lean_Parser_Attr_grindUsr___closed__2 = _init_l_Lean_Parser_Attr_grindUsr___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr___closed__2);
l_Lean_Parser_Attr_grindUsr___closed__3 = _init_l_Lean_Parser_Attr_grindUsr___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr___closed__3);
l_Lean_Parser_Attr_grindUsr___closed__4 = _init_l_Lean_Parser_Attr_grindUsr___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr___closed__4);
l_Lean_Parser_Attr_grindUsr___closed__5 = _init_l_Lean_Parser_Attr_grindUsr___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr___closed__5);
l_Lean_Parser_Attr_grindUsr = _init_l_Lean_Parser_Attr_grindUsr();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr);
l_Lean_Parser_Attr_grindCases___closed__1 = _init_l_Lean_Parser_Attr_grindCases___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases___closed__1);
l_Lean_Parser_Attr_grindCases___closed__2 = _init_l_Lean_Parser_Attr_grindCases___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases___closed__2);
l_Lean_Parser_Attr_grindCases___closed__3 = _init_l_Lean_Parser_Attr_grindCases___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases___closed__3);
l_Lean_Parser_Attr_grindCases___closed__4 = _init_l_Lean_Parser_Attr_grindCases___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases___closed__4);
l_Lean_Parser_Attr_grindCases___closed__5 = _init_l_Lean_Parser_Attr_grindCases___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases___closed__5);
l_Lean_Parser_Attr_grindCases = _init_l_Lean_Parser_Attr_grindCases();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases);
l_Lean_Parser_Attr_grindCasesEager___closed__1 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__1);
l_Lean_Parser_Attr_grindCasesEager___closed__2 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__2);
l_Lean_Parser_Attr_grindCasesEager___closed__3 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__3);
l_Lean_Parser_Attr_grindCasesEager___closed__4 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__4);
l_Lean_Parser_Attr_grindCasesEager___closed__5 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__5);
l_Lean_Parser_Attr_grindCasesEager___closed__6 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__6);
l_Lean_Parser_Attr_grindCasesEager___closed__7 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__7);
l_Lean_Parser_Attr_grindCasesEager___closed__8 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__8);
l_Lean_Parser_Attr_grindCasesEager___closed__9 = _init_l_Lean_Parser_Attr_grindCasesEager___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager___closed__9);
l_Lean_Parser_Attr_grindCasesEager = _init_l_Lean_Parser_Attr_grindCasesEager();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager);
l_Lean_Parser_Attr_grindIntro___closed__1 = _init_l_Lean_Parser_Attr_grindIntro___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro___closed__1);
l_Lean_Parser_Attr_grindIntro___closed__2 = _init_l_Lean_Parser_Attr_grindIntro___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro___closed__2);
l_Lean_Parser_Attr_grindIntro___closed__3 = _init_l_Lean_Parser_Attr_grindIntro___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro___closed__3);
l_Lean_Parser_Attr_grindIntro___closed__4 = _init_l_Lean_Parser_Attr_grindIntro___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro___closed__4);
l_Lean_Parser_Attr_grindIntro___closed__5 = _init_l_Lean_Parser_Attr_grindIntro___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro___closed__5);
l_Lean_Parser_Attr_grindIntro = _init_l_Lean_Parser_Attr_grindIntro();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro);
l_Lean_Parser_Attr_grindMod___closed__1 = _init_l_Lean_Parser_Attr_grindMod___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__1);
l_Lean_Parser_Attr_grindMod___closed__2 = _init_l_Lean_Parser_Attr_grindMod___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__2);
l_Lean_Parser_Attr_grindMod___closed__3 = _init_l_Lean_Parser_Attr_grindMod___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__3);
l_Lean_Parser_Attr_grindMod___closed__4 = _init_l_Lean_Parser_Attr_grindMod___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__4);
l_Lean_Parser_Attr_grindMod___closed__5 = _init_l_Lean_Parser_Attr_grindMod___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__5);
l_Lean_Parser_Attr_grindMod___closed__6 = _init_l_Lean_Parser_Attr_grindMod___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__6);
l_Lean_Parser_Attr_grindMod___closed__7 = _init_l_Lean_Parser_Attr_grindMod___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__7);
l_Lean_Parser_Attr_grindMod___closed__8 = _init_l_Lean_Parser_Attr_grindMod___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__8);
l_Lean_Parser_Attr_grindMod___closed__9 = _init_l_Lean_Parser_Attr_grindMod___closed__9();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__9);
l_Lean_Parser_Attr_grindMod___closed__10 = _init_l_Lean_Parser_Attr_grindMod___closed__10();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__10);
l_Lean_Parser_Attr_grindMod___closed__11 = _init_l_Lean_Parser_Attr_grindMod___closed__11();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__11);
l_Lean_Parser_Attr_grindMod___closed__12 = _init_l_Lean_Parser_Attr_grindMod___closed__12();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__12);
l_Lean_Parser_Attr_grindMod___closed__13 = _init_l_Lean_Parser_Attr_grindMod___closed__13();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__13);
l_Lean_Parser_Attr_grindMod___closed__14 = _init_l_Lean_Parser_Attr_grindMod___closed__14();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__14);
l_Lean_Parser_Attr_grindMod = _init_l_Lean_Parser_Attr_grindMod();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod);
l_Lean_Parser_Attr_grind___closed__1 = _init_l_Lean_Parser_Attr_grind___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__1);
l_Lean_Parser_Attr_grind___closed__2 = _init_l_Lean_Parser_Attr_grind___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__2);
l_Lean_Parser_Attr_grind___closed__3 = _init_l_Lean_Parser_Attr_grind___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__3);
l_Lean_Parser_Attr_grind___closed__4 = _init_l_Lean_Parser_Attr_grind___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__4);
l_Lean_Parser_Attr_grind___closed__5 = _init_l_Lean_Parser_Attr_grind___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__5);
l_Lean_Parser_Attr_grind___closed__6 = _init_l_Lean_Parser_Attr_grind___closed__6();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__6);
l_Lean_Parser_Attr_grind___closed__7 = _init_l_Lean_Parser_Attr_grind___closed__7();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__7);
l_Lean_Parser_Attr_grind___closed__8 = _init_l_Lean_Parser_Attr_grind___closed__8();
lean_mark_persistent(l_Lean_Parser_Attr_grind___closed__8);
l_Lean_Parser_Attr_grind = _init_l_Lean_Parser_Attr_grind();
lean_mark_persistent(l_Lean_Parser_Attr_grind);
l_Lean_Grind_instInhabitedConfig___closed__1 = _init_l_Lean_Grind_instInhabitedConfig___closed__1();
lean_mark_persistent(l_Lean_Grind_instInhabitedConfig___closed__1);
l_Lean_Grind_instInhabitedConfig = _init_l_Lean_Grind_instInhabitedConfig();
lean_mark_persistent(l_Lean_Grind_instInhabitedConfig);
l_Lean_Grind_instBEqConfig___closed__1 = _init_l_Lean_Grind_instBEqConfig___closed__1();
lean_mark_persistent(l_Lean_Grind_instBEqConfig___closed__1);
l_Lean_Grind_instBEqConfig = _init_l_Lean_Grind_instBEqConfig();
lean_mark_persistent(l_Lean_Grind_instBEqConfig);
l_Lean_Parser_Tactic_grindErase___closed__1 = _init_l_Lean_Parser_Tactic_grindErase___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__1);
l_Lean_Parser_Tactic_grindErase___closed__2 = _init_l_Lean_Parser_Tactic_grindErase___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__2);
l_Lean_Parser_Tactic_grindErase___closed__3 = _init_l_Lean_Parser_Tactic_grindErase___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__3);
l_Lean_Parser_Tactic_grindErase___closed__4 = _init_l_Lean_Parser_Tactic_grindErase___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__4);
l_Lean_Parser_Tactic_grindErase___closed__5 = _init_l_Lean_Parser_Tactic_grindErase___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__5);
l_Lean_Parser_Tactic_grindErase___closed__6 = _init_l_Lean_Parser_Tactic_grindErase___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__6);
l_Lean_Parser_Tactic_grindErase___closed__7 = _init_l_Lean_Parser_Tactic_grindErase___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__7);
l_Lean_Parser_Tactic_grindErase___closed__8 = _init_l_Lean_Parser_Tactic_grindErase___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__8);
l_Lean_Parser_Tactic_grindErase___closed__9 = _init_l_Lean_Parser_Tactic_grindErase___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__9);
l_Lean_Parser_Tactic_grindErase___closed__10 = _init_l_Lean_Parser_Tactic_grindErase___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase___closed__10);
l_Lean_Parser_Tactic_grindErase = _init_l_Lean_Parser_Tactic_grindErase();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase);
l_Lean_Parser_Tactic_grindLemma___closed__1 = _init_l_Lean_Parser_Tactic_grindLemma___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma___closed__1);
l_Lean_Parser_Tactic_grindLemma___closed__2 = _init_l_Lean_Parser_Tactic_grindLemma___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma___closed__2);
l_Lean_Parser_Tactic_grindLemma___closed__3 = _init_l_Lean_Parser_Tactic_grindLemma___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma___closed__3);
l_Lean_Parser_Tactic_grindLemma___closed__4 = _init_l_Lean_Parser_Tactic_grindLemma___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma___closed__4);
l_Lean_Parser_Tactic_grindLemma = _init_l_Lean_Parser_Tactic_grindLemma();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma);
l_Lean_Parser_Tactic_grindParam___closed__1 = _init_l_Lean_Parser_Tactic_grindParam___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam___closed__1);
l_Lean_Parser_Tactic_grindParam___closed__2 = _init_l_Lean_Parser_Tactic_grindParam___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam___closed__2);
l_Lean_Parser_Tactic_grindParam___closed__3 = _init_l_Lean_Parser_Tactic_grindParam___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam___closed__3);
l_Lean_Parser_Tactic_grindParam___closed__4 = _init_l_Lean_Parser_Tactic_grindParam___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam___closed__4);
l_Lean_Parser_Tactic_grindParam = _init_l_Lean_Parser_Tactic_grindParam();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam);
l_Lean_Parser_Tactic_grind___closed__1 = _init_l_Lean_Parser_Tactic_grind___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__1);
l_Lean_Parser_Tactic_grind___closed__2 = _init_l_Lean_Parser_Tactic_grind___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__2);
l_Lean_Parser_Tactic_grind___closed__3 = _init_l_Lean_Parser_Tactic_grind___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__3);
l_Lean_Parser_Tactic_grind___closed__4 = _init_l_Lean_Parser_Tactic_grind___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__4);
l_Lean_Parser_Tactic_grind___closed__5 = _init_l_Lean_Parser_Tactic_grind___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__5);
l_Lean_Parser_Tactic_grind___closed__6 = _init_l_Lean_Parser_Tactic_grind___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__6);
l_Lean_Parser_Tactic_grind___closed__7 = _init_l_Lean_Parser_Tactic_grind___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__7);
l_Lean_Parser_Tactic_grind___closed__8 = _init_l_Lean_Parser_Tactic_grind___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__8);
l_Lean_Parser_Tactic_grind___closed__9 = _init_l_Lean_Parser_Tactic_grind___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__9);
l_Lean_Parser_Tactic_grind___closed__10 = _init_l_Lean_Parser_Tactic_grind___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__10);
l_Lean_Parser_Tactic_grind___closed__11 = _init_l_Lean_Parser_Tactic_grind___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__11);
l_Lean_Parser_Tactic_grind___closed__12 = _init_l_Lean_Parser_Tactic_grind___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__12);
l_Lean_Parser_Tactic_grind___closed__13 = _init_l_Lean_Parser_Tactic_grind___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__13);
l_Lean_Parser_Tactic_grind___closed__14 = _init_l_Lean_Parser_Tactic_grind___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__14);
l_Lean_Parser_Tactic_grind___closed__15 = _init_l_Lean_Parser_Tactic_grind___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__15);
l_Lean_Parser_Tactic_grind___closed__16 = _init_l_Lean_Parser_Tactic_grind___closed__16();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__16);
l_Lean_Parser_Tactic_grind___closed__17 = _init_l_Lean_Parser_Tactic_grind___closed__17();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__17);
l_Lean_Parser_Tactic_grind___closed__18 = _init_l_Lean_Parser_Tactic_grind___closed__18();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__18);
l_Lean_Parser_Tactic_grind___closed__19 = _init_l_Lean_Parser_Tactic_grind___closed__19();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__19);
l_Lean_Parser_Tactic_grind___closed__20 = _init_l_Lean_Parser_Tactic_grind___closed__20();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__20);
l_Lean_Parser_Tactic_grind___closed__21 = _init_l_Lean_Parser_Tactic_grind___closed__21();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__21);
l_Lean_Parser_Tactic_grind___closed__22 = _init_l_Lean_Parser_Tactic_grind___closed__22();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__22);
l_Lean_Parser_Tactic_grind___closed__23 = _init_l_Lean_Parser_Tactic_grind___closed__23();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__23);
l_Lean_Parser_Tactic_grind___closed__24 = _init_l_Lean_Parser_Tactic_grind___closed__24();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__24);
l_Lean_Parser_Tactic_grind___closed__25 = _init_l_Lean_Parser_Tactic_grind___closed__25();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__25);
l_Lean_Parser_Tactic_grind___closed__26 = _init_l_Lean_Parser_Tactic_grind___closed__26();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__26);
l_Lean_Parser_Tactic_grind___closed__27 = _init_l_Lean_Parser_Tactic_grind___closed__27();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__27);
l_Lean_Parser_Tactic_grind___closed__28 = _init_l_Lean_Parser_Tactic_grind___closed__28();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__28);
l_Lean_Parser_Tactic_grind___closed__29 = _init_l_Lean_Parser_Tactic_grind___closed__29();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__29);
l_Lean_Parser_Tactic_grind___closed__30 = _init_l_Lean_Parser_Tactic_grind___closed__30();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__30);
l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
lean_mark_persistent(l_Lean_Parser_Tactic_grind);
l_Lean_Parser_Tactic_grindTrace___closed__1 = _init_l_Lean_Parser_Tactic_grindTrace___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__1);
l_Lean_Parser_Tactic_grindTrace___closed__2 = _init_l_Lean_Parser_Tactic_grindTrace___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__2);
l_Lean_Parser_Tactic_grindTrace___closed__3 = _init_l_Lean_Parser_Tactic_grindTrace___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__3);
l_Lean_Parser_Tactic_grindTrace___closed__4 = _init_l_Lean_Parser_Tactic_grindTrace___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__4);
l_Lean_Parser_Tactic_grindTrace___closed__5 = _init_l_Lean_Parser_Tactic_grindTrace___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__5);
l_Lean_Parser_Tactic_grindTrace___closed__6 = _init_l_Lean_Parser_Tactic_grindTrace___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__6);
l_Lean_Parser_Tactic_grindTrace___closed__7 = _init_l_Lean_Parser_Tactic_grindTrace___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__7);
l_Lean_Parser_Tactic_grindTrace___closed__8 = _init_l_Lean_Parser_Tactic_grindTrace___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__8);
l_Lean_Parser_Tactic_grindTrace___closed__9 = _init_l_Lean_Parser_Tactic_grindTrace___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace___closed__9);
l_Lean_Parser_Tactic_grindTrace = _init_l_Lean_Parser_Tactic_grindTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
