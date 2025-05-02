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
static lean_object* l_Lean_Parser_Attr_grindExt___closed__2;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__4;
static lean_object* l_Lean_Parser_Attr_grindEqBoth___closed__15;
static lean_object* l_Lean_Parser_Tactic_grind___closed__7;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__5;
static lean_object* l_Lean_Parser_Tactic_grind___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindUsr;
static lean_object* l_Lean_Parser_Attr_grindExt___closed__5;
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
static lean_object* l_Lean_Parser_Attr_grindExt___closed__3;
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
static lean_object* l_Lean_Parser_Attr_grindExt___closed__4;
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Attr_grindBwd___closed__2;
static lean_object* l_Lean_Parser_Attr_grindMod___closed__15;
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
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410_(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindExt;
static lean_object* l_Lean_Parser_Tactic_grind___closed__16;
static lean_object* l_Lean_Parser_Tactic_grind___closed__12;
static lean_object* l_Lean_Parser_Attr_grindExt___closed__1;
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
static lean_object* _init_l_Lean_Parser_Attr_grindExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindExt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_resetGrindAttrs___closed__1;
x_2 = l_Lean_Parser_resetGrindAttrs___closed__2;
x_3 = l_Lean_Parser_Attr_grindEq___closed__1;
x_4 = l_Lean_Parser_Attr_grindExt___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ext ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindExt___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Attr_grindExt___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindExt___closed__1;
x_2 = l_Lean_Parser_Attr_grindExt___closed__2;
x_3 = l_Lean_Parser_Attr_grindExt___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindExt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Attr_grindExt___closed__5;
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
x_2 = l_Lean_Parser_Attr_grindIntro;
x_3 = l_Lean_Parser_Attr_grindExt;
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
x_2 = l_Lean_Parser_Attr_grindCases;
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
x_2 = l_Lean_Parser_Attr_grindCasesEager;
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
x_2 = l_Lean_Parser_Attr_grindUsr;
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
x_2 = l_Lean_Parser_Attr_grindLR;
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
x_2 = l_Lean_Parser_Attr_grindRL;
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
x_2 = l_Lean_Parser_Attr_grindFwd;
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
x_2 = l_Lean_Parser_Attr_grindBwd;
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
x_2 = l_Lean_Parser_Attr_grindEqBwd;
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
x_2 = l_Lean_Parser_Attr_grindEq;
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
x_2 = l_Lean_Parser_Attr_grindEqRhs;
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
x_1 = l_Lean_Parser_Attr_grindEqBwd___closed__4;
x_2 = l_Lean_Parser_Attr_grindEqBoth;
x_3 = l_Lean_Parser_Attr_grindMod___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Attr_grindMod___closed__1;
x_2 = l_Lean_Parser_Attr_grindMod___closed__2;
x_3 = l_Lean_Parser_Attr_grindMod___closed__14;
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
x_1 = l_Lean_Parser_Attr_grindMod___closed__15;
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
x_3 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*7, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 2, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 3, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 4, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 5, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 6, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 7, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 8, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 9, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 10, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 11, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 12, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 13, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 14, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 15, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 16, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 17, x_1);
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
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_60; uint8_t x_67; uint8_t x_74; uint8_t x_81; uint8_t x_88; uint8_t x_95; uint8_t x_102; uint8_t x_109; uint8_t x_116; uint8_t x_123; uint8_t x_130; uint8_t x_141; uint8_t x_148; uint8_t x_155; uint8_t x_162; uint8_t x_169; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 4);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 5);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 7);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 9);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 10);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 11);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 12);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 13);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 14);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 15);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 16);
x_26 = lean_ctor_get(x_1, 6);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 17);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 5);
x_38 = lean_ctor_get(x_2, 4);
x_39 = lean_ctor_get(x_2, 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 6);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 7);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 11);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 12);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 13);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 14);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 15);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 16);
x_51 = lean_ctor_get(x_2, 6);
x_52 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 17);
if (x_3 == 0)
{
if (x_28 == 0)
{
uint8_t x_184; 
x_184 = 1;
x_169 = x_184;
goto block_183;
}
else
{
uint8_t x_185; 
x_185 = 0;
x_169 = x_185;
goto block_183;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_186; 
x_186 = 0;
x_169 = x_186;
goto block_183;
}
else
{
uint8_t x_187; 
x_187 = 1;
x_169 = x_187;
goto block_183;
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
uint8_t x_55; 
x_55 = lean_nat_dec_eq(x_26, x_51);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = 0;
return x_56;
}
else
{
if (x_27 == 0)
{
if (x_52 == 0)
{
uint8_t x_57; 
x_57 = 1;
return x_57;
}
else
{
uint8_t x_58; 
x_58 = 0;
return x_58;
}
}
else
{
return x_52;
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
if (x_25 == 0)
{
if (x_50 == 0)
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
if (x_50 == 0)
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
if (x_24 == 0)
{
if (x_49 == 0)
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
if (x_49 == 0)
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
if (x_23 == 0)
{
if (x_48 == 0)
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
if (x_48 == 0)
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
block_87:
{
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = 0;
return x_82;
}
else
{
if (x_22 == 0)
{
if (x_47 == 0)
{
uint8_t x_83; 
x_83 = 1;
x_74 = x_83;
goto block_80;
}
else
{
uint8_t x_84; 
x_84 = 0;
x_74 = x_84;
goto block_80;
}
}
else
{
if (x_47 == 0)
{
uint8_t x_85; 
x_85 = 0;
x_74 = x_85;
goto block_80;
}
else
{
uint8_t x_86; 
x_86 = 1;
x_74 = x_86;
goto block_80;
}
}
}
}
block_94:
{
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = 0;
return x_89;
}
else
{
if (x_21 == 0)
{
if (x_46 == 0)
{
uint8_t x_90; 
x_90 = 1;
x_81 = x_90;
goto block_87;
}
else
{
uint8_t x_91; 
x_91 = 0;
x_81 = x_91;
goto block_87;
}
}
else
{
if (x_46 == 0)
{
uint8_t x_92; 
x_92 = 0;
x_81 = x_92;
goto block_87;
}
else
{
uint8_t x_93; 
x_93 = 1;
x_81 = x_93;
goto block_87;
}
}
}
}
block_101:
{
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = 0;
return x_96;
}
else
{
if (x_20 == 0)
{
if (x_45 == 0)
{
uint8_t x_97; 
x_97 = 1;
x_88 = x_97;
goto block_94;
}
else
{
uint8_t x_98; 
x_98 = 0;
x_88 = x_98;
goto block_94;
}
}
else
{
if (x_45 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_88 = x_99;
goto block_94;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_88 = x_100;
goto block_94;
}
}
}
}
block_108:
{
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = 0;
return x_103;
}
else
{
if (x_19 == 0)
{
if (x_44 == 0)
{
uint8_t x_104; 
x_104 = 1;
x_95 = x_104;
goto block_101;
}
else
{
uint8_t x_105; 
x_105 = 0;
x_95 = x_105;
goto block_101;
}
}
else
{
if (x_44 == 0)
{
uint8_t x_106; 
x_106 = 0;
x_95 = x_106;
goto block_101;
}
else
{
uint8_t x_107; 
x_107 = 1;
x_95 = x_107;
goto block_101;
}
}
}
}
block_115:
{
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = 0;
return x_110;
}
else
{
if (x_18 == 0)
{
if (x_43 == 0)
{
uint8_t x_111; 
x_111 = 1;
x_102 = x_111;
goto block_108;
}
else
{
uint8_t x_112; 
x_112 = 0;
x_102 = x_112;
goto block_108;
}
}
else
{
if (x_43 == 0)
{
uint8_t x_113; 
x_113 = 0;
x_102 = x_113;
goto block_108;
}
else
{
uint8_t x_114; 
x_114 = 1;
x_102 = x_114;
goto block_108;
}
}
}
}
block_122:
{
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = 0;
return x_117;
}
else
{
if (x_17 == 0)
{
if (x_42 == 0)
{
uint8_t x_118; 
x_118 = 1;
x_109 = x_118;
goto block_115;
}
else
{
uint8_t x_119; 
x_119 = 0;
x_109 = x_119;
goto block_115;
}
}
else
{
if (x_42 == 0)
{
uint8_t x_120; 
x_120 = 0;
x_109 = x_120;
goto block_115;
}
else
{
uint8_t x_121; 
x_121 = 1;
x_109 = x_121;
goto block_115;
}
}
}
}
block_129:
{
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = 0;
return x_124;
}
else
{
if (x_16 == 0)
{
if (x_41 == 0)
{
uint8_t x_125; 
x_125 = 1;
x_116 = x_125;
goto block_122;
}
else
{
uint8_t x_126; 
x_126 = 0;
x_116 = x_126;
goto block_122;
}
}
else
{
if (x_41 == 0)
{
uint8_t x_127; 
x_127 = 0;
x_116 = x_127;
goto block_122;
}
else
{
uint8_t x_128; 
x_128 = 1;
x_116 = x_128;
goto block_122;
}
}
}
}
block_140:
{
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = 0;
return x_131;
}
else
{
uint8_t x_132; 
x_132 = lean_nat_dec_eq(x_13, x_38);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = 0;
return x_133;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_eq(x_14, x_39);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = 0;
return x_135;
}
else
{
if (x_15 == 0)
{
if (x_40 == 0)
{
uint8_t x_136; 
x_136 = 1;
x_123 = x_136;
goto block_129;
}
else
{
uint8_t x_137; 
x_137 = 0;
x_123 = x_137;
goto block_129;
}
}
else
{
if (x_40 == 0)
{
uint8_t x_138; 
x_138 = 0;
x_123 = x_138;
goto block_129;
}
else
{
uint8_t x_139; 
x_139 = 1;
x_123 = x_139;
goto block_129;
}
}
}
}
}
}
block_147:
{
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = 0;
return x_142;
}
else
{
if (x_12 == 0)
{
if (x_37 == 0)
{
uint8_t x_143; 
x_143 = 1;
x_130 = x_143;
goto block_140;
}
else
{
uint8_t x_144; 
x_144 = 0;
x_130 = x_144;
goto block_140;
}
}
else
{
if (x_37 == 0)
{
uint8_t x_145; 
x_145 = 0;
x_130 = x_145;
goto block_140;
}
else
{
uint8_t x_146; 
x_146 = 1;
x_130 = x_146;
goto block_140;
}
}
}
}
block_154:
{
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = 0;
return x_149;
}
else
{
if (x_11 == 0)
{
if (x_36 == 0)
{
uint8_t x_150; 
x_150 = 1;
x_141 = x_150;
goto block_147;
}
else
{
uint8_t x_151; 
x_151 = 0;
x_141 = x_151;
goto block_147;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_152; 
x_152 = 0;
x_141 = x_152;
goto block_147;
}
else
{
uint8_t x_153; 
x_153 = 1;
x_141 = x_153;
goto block_147;
}
}
}
}
block_161:
{
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = 0;
return x_156;
}
else
{
if (x_10 == 0)
{
if (x_35 == 0)
{
uint8_t x_157; 
x_157 = 1;
x_148 = x_157;
goto block_154;
}
else
{
uint8_t x_158; 
x_158 = 0;
x_148 = x_158;
goto block_154;
}
}
else
{
if (x_35 == 0)
{
uint8_t x_159; 
x_159 = 0;
x_148 = x_159;
goto block_154;
}
else
{
uint8_t x_160; 
x_160 = 1;
x_148 = x_160;
goto block_154;
}
}
}
}
block_168:
{
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = 0;
return x_163;
}
else
{
if (x_9 == 0)
{
if (x_34 == 0)
{
uint8_t x_164; 
x_164 = 1;
x_155 = x_164;
goto block_161;
}
else
{
uint8_t x_165; 
x_165 = 0;
x_155 = x_165;
goto block_161;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_166; 
x_166 = 0;
x_155 = x_166;
goto block_161;
}
else
{
uint8_t x_167; 
x_167 = 1;
x_155 = x_167;
goto block_161;
}
}
}
}
block_183:
{
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = 0;
return x_170;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_eq(x_4, x_29);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = 0;
return x_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_eq(x_5, x_30);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = 0;
return x_174;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_eq(x_6, x_31);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = 0;
return x_176;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_eq(x_7, x_32);
if (x_177 == 0)
{
uint8_t x_178; 
x_178 = 0;
return x_178;
}
else
{
if (x_8 == 0)
{
if (x_33 == 0)
{
uint8_t x_179; 
x_179 = 1;
x_162 = x_179;
goto block_168;
}
else
{
uint8_t x_180; 
x_180 = 0;
x_162 = x_180;
goto block_168;
}
}
else
{
if (x_33 == 0)
{
uint8_t x_181; 
x_181 = 0;
x_162 = x_181;
goto block_168;
}
else
{
uint8_t x_182; 
x_182 = 1;
x_162 = x_182;
goto block_168;
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410____boxed), 2, 0);
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
l_Lean_Parser_Attr_grindExt___closed__1 = _init_l_Lean_Parser_Attr_grindExt___closed__1();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt___closed__1);
l_Lean_Parser_Attr_grindExt___closed__2 = _init_l_Lean_Parser_Attr_grindExt___closed__2();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt___closed__2);
l_Lean_Parser_Attr_grindExt___closed__3 = _init_l_Lean_Parser_Attr_grindExt___closed__3();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt___closed__3);
l_Lean_Parser_Attr_grindExt___closed__4 = _init_l_Lean_Parser_Attr_grindExt___closed__4();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt___closed__4);
l_Lean_Parser_Attr_grindExt___closed__5 = _init_l_Lean_Parser_Attr_grindExt___closed__5();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt___closed__5);
l_Lean_Parser_Attr_grindExt = _init_l_Lean_Parser_Attr_grindExt();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt);
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
l_Lean_Parser_Attr_grindMod___closed__15 = _init_l_Lean_Parser_Attr_grindMod___closed__15();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod___closed__15);
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
