// Lean compiler output
// Module: Lean.Meta.Match.MVarRenaming
// Imports: Lean.Util.ReplaceExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__4;
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_mvarId_x21___spec__1(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_MVarRenaming_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_find_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_MVarRenaming_find_x21___closed__1;
x_2 = l_Lean_Meta_MVarRenaming_find_x21___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Meta_MVarRenaming_find_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_MVarRenaming_find_x21___closed__4;
x_5 = l_panic___at_Lean_Expr_mvarId_x21___spec__1(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_find_x21(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_Expr_mvar___override(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_Expr_mvar___override(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_2);
if (x_3 == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_MVarRenaming_apply___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_replace_expr(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_apply___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_apply(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ReplaceExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_MVarRenaming_find_x21___closed__1 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__1();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__1);
l_Lean_Meta_MVarRenaming_find_x21___closed__2 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__2();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__2);
l_Lean_Meta_MVarRenaming_find_x21___closed__3 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__3);
l_Lean_Meta_MVarRenaming_find_x21___closed__4 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__4();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
