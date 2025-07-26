// Lean compiler output
// Module: Std.Do.Triple.Basic
// Imports: Std.Do.WP Std.Do.SPred
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
static lean_object* l_Std_Do_unexpandTriple___closed__2;
static lean_object* l_Std_Do_triple___closed__0;
static lean_object* l_Std_Do_triple___closed__16;
static lean_object* l_Std_Do_triple___closed__4;
static lean_object* l_Std_Do_triple___closed__8;
static lean_object* l_Std_Do_triple___closed__21;
static lean_object* l_Std_Do_triple___closed__5;
static lean_object* l_Std_Do_unexpandTriple___closed__4;
static lean_object* l_Std_Do_triple___closed__12;
static lean_object* l_Std_Do_triple___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__20;
static lean_object* l_Std_Do_triple___closed__17;
static lean_object* l_Std_Do_triple___closed__10;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__22;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Std_Do_triple___closed__18;
static lean_object* l_Std_Do_triple___closed__2;
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__24;
static lean_object* l_Std_Do_triple___closed__11;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__9;
static lean_object* l_Std_Do_triple___closed__15;
static lean_object* l_Std_Do_triple___closed__23;
lean_object* l_Std_Do_SPred_Notation_unpack___at___Std_Do_SPred_Notation_unexpandEntails_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__7;
static lean_object* l_Std_Do_unexpandTriple___closed__1;
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__19;
LEAN_EXPORT lean_object* l_Std_Do_triple;
static lean_object* l_Std_Do_unexpandTriple___closed__3;
static lean_object* l_Std_Do_triple___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Do_triple___closed__13;
static lean_object* l_Std_Do_unexpandTriple___closed__0;
static lean_object* l_Std_Do_triple___closed__3;
static lean_object* l_Std_Do_triple___closed__14;
static lean_object* _init_l_Std_Do_triple___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Do", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("triple", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__2;
x_2 = l_Std_Do_triple___closed__1;
x_3 = l_Std_Do_triple___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Do_triple___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Do_triple___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⦃", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Do_triple___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Do_triple___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Do_triple___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Do_triple___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Do_triple___closed__9;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Do_triple___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__10;
x_2 = l_Std_Do_triple___closed__7;
x_3 = l_Std_Do_triple___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⦄ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Do_triple___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Do_triple___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__13;
x_2 = l_Std_Do_triple___closed__11;
x_3 = l_Std_Do_triple___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1022u);
x_2 = l_Std_Do_triple___closed__9;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Do_triple___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__15;
x_2 = l_Std_Do_triple___closed__14;
x_3 = l_Std_Do_triple___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ⦃", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Do_triple___closed__17;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Do_triple___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__18;
x_2 = l_Std_Do_triple___closed__16;
x_3 = l_Std_Do_triple___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__10;
x_2 = l_Std_Do_triple___closed__19;
x_3 = l_Std_Do_triple___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⦄", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Do_triple___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Do_triple___closed__21;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Do_triple___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__22;
x_2 = l_Std_Do_triple___closed__20;
x_3 = l_Std_Do_triple___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Do_triple___closed__23;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Std_Do_triple___closed__3;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Do_triple() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Do_triple___closed__24;
return x_1;
}
}
static lean_object* _init_l_Std_Do_unexpandTriple___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Do_unexpandTriple___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Do_unexpandTriple___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Do_unexpandTriple___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Do_unexpandTriple___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Do_unexpandTriple___closed__3;
x_2 = l_Std_Do_unexpandTriple___closed__2;
x_3 = l_Std_Do_unexpandTriple___closed__1;
x_4 = l_Std_Do_unexpandTriple___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Std_Do_unexpandTriple___closed__4;
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
x_10 = lean_unsigned_to_nat(3u);
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Syntax_getArg(x_9, x_8);
x_15 = l_Std_Do_SPred_Notation_unpack___at___Std_Do_SPred_Notation_unexpandEntails_spec__0(x_14, x_2, x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_9, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_9, x_20);
lean_dec(x_9);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_2, x_22);
x_24 = l_Std_Do_triple___closed__3;
x_25 = l_Std_Do_triple___closed__6;
lean_inc(x_23);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Do_triple___closed__21;
lean_inc(x_23);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_28);
lean_inc_ref(x_26);
x_29 = l_Lean_Syntax_node7(x_23, x_24, x_26, x_17, x_28, x_19, x_26, x_21, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_9, x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = l_Lean_Syntax_getArg(x_9, x_34);
lean_dec(x_9);
x_36 = 0;
x_37 = l_Lean_SourceInfo_fromRef(x_2, x_36);
x_38 = l_Std_Do_triple___closed__3;
x_39 = l_Std_Do_triple___closed__6;
lean_inc(x_37);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Std_Do_triple___closed__21;
lean_inc(x_37);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
lean_inc_ref(x_42);
lean_inc_ref(x_40);
x_43 = l_Lean_Syntax_node7(x_37, x_38, x_40, x_30, x_42, x_33, x_40, x_35, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Do_unexpandTriple(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Std_Do_WP(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Do_SPred(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_Triple_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_WP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_SPred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Do_triple___closed__0 = _init_l_Std_Do_triple___closed__0();
lean_mark_persistent(l_Std_Do_triple___closed__0);
l_Std_Do_triple___closed__1 = _init_l_Std_Do_triple___closed__1();
lean_mark_persistent(l_Std_Do_triple___closed__1);
l_Std_Do_triple___closed__2 = _init_l_Std_Do_triple___closed__2();
lean_mark_persistent(l_Std_Do_triple___closed__2);
l_Std_Do_triple___closed__3 = _init_l_Std_Do_triple___closed__3();
lean_mark_persistent(l_Std_Do_triple___closed__3);
l_Std_Do_triple___closed__4 = _init_l_Std_Do_triple___closed__4();
lean_mark_persistent(l_Std_Do_triple___closed__4);
l_Std_Do_triple___closed__5 = _init_l_Std_Do_triple___closed__5();
lean_mark_persistent(l_Std_Do_triple___closed__5);
l_Std_Do_triple___closed__6 = _init_l_Std_Do_triple___closed__6();
lean_mark_persistent(l_Std_Do_triple___closed__6);
l_Std_Do_triple___closed__7 = _init_l_Std_Do_triple___closed__7();
lean_mark_persistent(l_Std_Do_triple___closed__7);
l_Std_Do_triple___closed__8 = _init_l_Std_Do_triple___closed__8();
lean_mark_persistent(l_Std_Do_triple___closed__8);
l_Std_Do_triple___closed__9 = _init_l_Std_Do_triple___closed__9();
lean_mark_persistent(l_Std_Do_triple___closed__9);
l_Std_Do_triple___closed__10 = _init_l_Std_Do_triple___closed__10();
lean_mark_persistent(l_Std_Do_triple___closed__10);
l_Std_Do_triple___closed__11 = _init_l_Std_Do_triple___closed__11();
lean_mark_persistent(l_Std_Do_triple___closed__11);
l_Std_Do_triple___closed__12 = _init_l_Std_Do_triple___closed__12();
lean_mark_persistent(l_Std_Do_triple___closed__12);
l_Std_Do_triple___closed__13 = _init_l_Std_Do_triple___closed__13();
lean_mark_persistent(l_Std_Do_triple___closed__13);
l_Std_Do_triple___closed__14 = _init_l_Std_Do_triple___closed__14();
lean_mark_persistent(l_Std_Do_triple___closed__14);
l_Std_Do_triple___closed__15 = _init_l_Std_Do_triple___closed__15();
lean_mark_persistent(l_Std_Do_triple___closed__15);
l_Std_Do_triple___closed__16 = _init_l_Std_Do_triple___closed__16();
lean_mark_persistent(l_Std_Do_triple___closed__16);
l_Std_Do_triple___closed__17 = _init_l_Std_Do_triple___closed__17();
lean_mark_persistent(l_Std_Do_triple___closed__17);
l_Std_Do_triple___closed__18 = _init_l_Std_Do_triple___closed__18();
lean_mark_persistent(l_Std_Do_triple___closed__18);
l_Std_Do_triple___closed__19 = _init_l_Std_Do_triple___closed__19();
lean_mark_persistent(l_Std_Do_triple___closed__19);
l_Std_Do_triple___closed__20 = _init_l_Std_Do_triple___closed__20();
lean_mark_persistent(l_Std_Do_triple___closed__20);
l_Std_Do_triple___closed__21 = _init_l_Std_Do_triple___closed__21();
lean_mark_persistent(l_Std_Do_triple___closed__21);
l_Std_Do_triple___closed__22 = _init_l_Std_Do_triple___closed__22();
lean_mark_persistent(l_Std_Do_triple___closed__22);
l_Std_Do_triple___closed__23 = _init_l_Std_Do_triple___closed__23();
lean_mark_persistent(l_Std_Do_triple___closed__23);
l_Std_Do_triple___closed__24 = _init_l_Std_Do_triple___closed__24();
lean_mark_persistent(l_Std_Do_triple___closed__24);
l_Std_Do_triple = _init_l_Std_Do_triple();
lean_mark_persistent(l_Std_Do_triple);
l_Std_Do_unexpandTriple___closed__0 = _init_l_Std_Do_unexpandTriple___closed__0();
lean_mark_persistent(l_Std_Do_unexpandTriple___closed__0);
l_Std_Do_unexpandTriple___closed__1 = _init_l_Std_Do_unexpandTriple___closed__1();
lean_mark_persistent(l_Std_Do_unexpandTriple___closed__1);
l_Std_Do_unexpandTriple___closed__2 = _init_l_Std_Do_unexpandTriple___closed__2();
lean_mark_persistent(l_Std_Do_unexpandTriple___closed__2);
l_Std_Do_unexpandTriple___closed__3 = _init_l_Std_Do_unexpandTriple___closed__3();
lean_mark_persistent(l_Std_Do_unexpandTriple___closed__3);
l_Std_Do_unexpandTriple___closed__4 = _init_l_Std_Do_unexpandTriple___closed__4();
lean_mark_persistent(l_Std_Do_unexpandTriple___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
