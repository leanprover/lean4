// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Action
// Imports: public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_lia___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___closed__3;
static lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_lia(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_lia___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___closed__0;
lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___closed__5;
static lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___closed__4;
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lia", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__4;
x_2 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__3;
x_3 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__2;
x_4 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__1;
x_5 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_lia___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = 0;
x_11 = l_Lean_SourceInfo_fromRef(x_9, x_10);
x_12 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__4;
x_13 = l_Lean_Meta_Grind_Action_lia___lam__0___closed__5;
lean_inc(x_11);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Syntax_node1(x_11, x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_lia___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_check), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_lia(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_lia___lam__0___boxed), 8, 0);
x_13 = l_Lean_Meta_Grind_Action_lia___closed__0;
x_14 = l_Lean_Meta_Grind_Action_terminalAction(x_13, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_lia___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Action_lia___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Action(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Action_lia___lam__0___closed__0 = _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___lam__0___closed__0);
l_Lean_Meta_Grind_Action_lia___lam__0___closed__1 = _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___lam__0___closed__1);
l_Lean_Meta_Grind_Action_lia___lam__0___closed__2 = _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___lam__0___closed__2);
l_Lean_Meta_Grind_Action_lia___lam__0___closed__3 = _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___lam__0___closed__3);
l_Lean_Meta_Grind_Action_lia___lam__0___closed__4 = _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___lam__0___closed__4);
l_Lean_Meta_Grind_Action_lia___lam__0___closed__5 = _init_l_Lean_Meta_Grind_Action_lia___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___lam__0___closed__5);
l_Lean_Meta_Grind_Action_lia___closed__0 = _init_l_Lean_Meta_Grind_Action_lia___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_lia___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
