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
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_379_(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_379____boxed(lean_object*, lean_object*);
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
x_3 = lean_alloc_ctor(0, 6, 14);
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
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 13, x_1);
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
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_379_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_48; uint8_t x_55; uint8_t x_62; uint8_t x_69; uint8_t x_76; uint8_t x_83; uint8_t x_90; uint8_t x_101; uint8_t x_108; uint8_t x_115; uint8_t x_122; uint8_t x_129; 
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
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 13);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 2);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 3);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 4);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 5);
x_33 = lean_ctor_get(x_2, 4);
x_34 = lean_ctor_get(x_2, 5);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 6);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 7);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 8);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 9);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 10);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 11);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 12);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 13);
if (x_3 == 0)
{
if (x_23 == 0)
{
uint8_t x_144; 
x_144 = 1;
x_129 = x_144;
goto block_143;
}
else
{
uint8_t x_145; 
x_145 = 0;
x_129 = x_145;
goto block_143;
}
}
else
{
if (x_23 == 0)
{
uint8_t x_146; 
x_146 = 0;
x_129 = x_146;
goto block_143;
}
else
{
uint8_t x_147; 
x_147 = 1;
x_129 = x_147;
goto block_143;
}
}
block_47:
{
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
else
{
if (x_22 == 0)
{
if (x_42 == 0)
{
uint8_t x_45; 
x_45 = 1;
return x_45;
}
else
{
uint8_t x_46; 
x_46 = 0;
return x_46;
}
}
else
{
return x_42;
}
}
}
block_54:
{
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 0;
return x_49;
}
else
{
if (x_21 == 0)
{
if (x_41 == 0)
{
uint8_t x_50; 
x_50 = 1;
x_43 = x_50;
goto block_47;
}
else
{
uint8_t x_51; 
x_51 = 0;
x_43 = x_51;
goto block_47;
}
}
else
{
if (x_41 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_43 = x_52;
goto block_47;
}
else
{
uint8_t x_53; 
x_53 = 1;
x_43 = x_53;
goto block_47;
}
}
}
}
block_61:
{
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = 0;
return x_56;
}
else
{
if (x_20 == 0)
{
if (x_40 == 0)
{
uint8_t x_57; 
x_57 = 1;
x_48 = x_57;
goto block_54;
}
else
{
uint8_t x_58; 
x_58 = 0;
x_48 = x_58;
goto block_54;
}
}
else
{
if (x_40 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_48 = x_59;
goto block_54;
}
else
{
uint8_t x_60; 
x_60 = 1;
x_48 = x_60;
goto block_54;
}
}
}
}
block_68:
{
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
return x_63;
}
else
{
if (x_19 == 0)
{
if (x_39 == 0)
{
uint8_t x_64; 
x_64 = 1;
x_55 = x_64;
goto block_61;
}
else
{
uint8_t x_65; 
x_65 = 0;
x_55 = x_65;
goto block_61;
}
}
else
{
if (x_39 == 0)
{
uint8_t x_66; 
x_66 = 0;
x_55 = x_66;
goto block_61;
}
else
{
uint8_t x_67; 
x_67 = 1;
x_55 = x_67;
goto block_61;
}
}
}
}
block_75:
{
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
return x_70;
}
else
{
if (x_18 == 0)
{
if (x_38 == 0)
{
uint8_t x_71; 
x_71 = 1;
x_62 = x_71;
goto block_68;
}
else
{
uint8_t x_72; 
x_72 = 0;
x_62 = x_72;
goto block_68;
}
}
else
{
if (x_38 == 0)
{
uint8_t x_73; 
x_73 = 0;
x_62 = x_73;
goto block_68;
}
else
{
uint8_t x_74; 
x_74 = 1;
x_62 = x_74;
goto block_68;
}
}
}
}
block_82:
{
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 0;
return x_77;
}
else
{
if (x_17 == 0)
{
if (x_37 == 0)
{
uint8_t x_78; 
x_78 = 1;
x_69 = x_78;
goto block_75;
}
else
{
uint8_t x_79; 
x_79 = 0;
x_69 = x_79;
goto block_75;
}
}
else
{
if (x_37 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_69 = x_80;
goto block_75;
}
else
{
uint8_t x_81; 
x_81 = 1;
x_69 = x_81;
goto block_75;
}
}
}
}
block_89:
{
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = 0;
return x_84;
}
else
{
if (x_16 == 0)
{
if (x_36 == 0)
{
uint8_t x_85; 
x_85 = 1;
x_76 = x_85;
goto block_82;
}
else
{
uint8_t x_86; 
x_86 = 0;
x_76 = x_86;
goto block_82;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_87; 
x_87 = 0;
x_76 = x_87;
goto block_82;
}
else
{
uint8_t x_88; 
x_88 = 1;
x_76 = x_88;
goto block_82;
}
}
}
}
block_100:
{
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = 0;
return x_91;
}
else
{
uint8_t x_92; 
x_92 = lean_nat_dec_eq(x_13, x_33);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_eq(x_14, x_34);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = 0;
return x_95;
}
else
{
if (x_15 == 0)
{
if (x_35 == 0)
{
uint8_t x_96; 
x_96 = 1;
x_83 = x_96;
goto block_89;
}
else
{
uint8_t x_97; 
x_97 = 0;
x_83 = x_97;
goto block_89;
}
}
else
{
if (x_35 == 0)
{
uint8_t x_98; 
x_98 = 0;
x_83 = x_98;
goto block_89;
}
else
{
uint8_t x_99; 
x_99 = 1;
x_83 = x_99;
goto block_89;
}
}
}
}
}
}
block_107:
{
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = 0;
return x_102;
}
else
{
if (x_12 == 0)
{
if (x_32 == 0)
{
uint8_t x_103; 
x_103 = 1;
x_90 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
x_104 = 0;
x_90 = x_104;
goto block_100;
}
}
else
{
if (x_32 == 0)
{
uint8_t x_105; 
x_105 = 0;
x_90 = x_105;
goto block_100;
}
else
{
uint8_t x_106; 
x_106 = 1;
x_90 = x_106;
goto block_100;
}
}
}
}
block_114:
{
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = 0;
return x_109;
}
else
{
if (x_11 == 0)
{
if (x_31 == 0)
{
uint8_t x_110; 
x_110 = 1;
x_101 = x_110;
goto block_107;
}
else
{
uint8_t x_111; 
x_111 = 0;
x_101 = x_111;
goto block_107;
}
}
else
{
if (x_31 == 0)
{
uint8_t x_112; 
x_112 = 0;
x_101 = x_112;
goto block_107;
}
else
{
uint8_t x_113; 
x_113 = 1;
x_101 = x_113;
goto block_107;
}
}
}
}
block_121:
{
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = 0;
return x_116;
}
else
{
if (x_10 == 0)
{
if (x_30 == 0)
{
uint8_t x_117; 
x_117 = 1;
x_108 = x_117;
goto block_114;
}
else
{
uint8_t x_118; 
x_118 = 0;
x_108 = x_118;
goto block_114;
}
}
else
{
if (x_30 == 0)
{
uint8_t x_119; 
x_119 = 0;
x_108 = x_119;
goto block_114;
}
else
{
uint8_t x_120; 
x_120 = 1;
x_108 = x_120;
goto block_114;
}
}
}
}
block_128:
{
if (x_122 == 0)
{
uint8_t x_123; 
x_123 = 0;
return x_123;
}
else
{
if (x_9 == 0)
{
if (x_29 == 0)
{
uint8_t x_124; 
x_124 = 1;
x_115 = x_124;
goto block_121;
}
else
{
uint8_t x_125; 
x_125 = 0;
x_115 = x_125;
goto block_121;
}
}
else
{
if (x_29 == 0)
{
uint8_t x_126; 
x_126 = 0;
x_115 = x_126;
goto block_121;
}
else
{
uint8_t x_127; 
x_127 = 1;
x_115 = x_127;
goto block_121;
}
}
}
}
block_143:
{
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 0;
return x_130;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_eq(x_4, x_24);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = 0;
return x_132;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_eq(x_5, x_25);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = 0;
return x_134;
}
else
{
uint8_t x_135; 
x_135 = lean_nat_dec_eq(x_6, x_26);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = 0;
return x_136;
}
else
{
uint8_t x_137; 
x_137 = lean_nat_dec_eq(x_7, x_27);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = 0;
return x_138;
}
else
{
if (x_8 == 0)
{
if (x_28 == 0)
{
uint8_t x_139; 
x_139 = 1;
x_122 = x_139;
goto block_128;
}
else
{
uint8_t x_140; 
x_140 = 0;
x_122 = x_140;
goto block_128;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_141; 
x_141 = 0;
x_122 = x_141;
goto block_128;
}
else
{
uint8_t x_142; 
x_142 = 1;
x_122 = x_142;
goto block_128;
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_379____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_379_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_379____boxed), 2, 0);
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
