// Lean compiler output
// Module: Lean.Elab.GenInjective
// Imports: Lean.Elab.Command Lean.Meta.Injective
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
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__7;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__3;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__5;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__2;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_1, x_2, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkInjectiveTheorems(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabGenInjectiveTheorems___lambda__1___boxed), 9, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Command_liftTermElabM___rarg(x_8, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabGenInjectiveTheorems___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabGenInjectiveTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabGenInjectiveTheorems(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("genInjectiveTheorems", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabGenInjectiveTheorems", 24);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabGenInjectiveTheorems___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8;
x_5 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__10;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__1;
x_2 = lean_unsigned_to_nat(45u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__2;
x_4 = lean_unsigned_to_nat(37u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__4;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__5;
x_4 = lean_unsigned_to_nat(73u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8;
x_3 = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_GenInjective(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__1);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__2);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__3);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__4);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__5);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__6);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__7);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__8);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__9 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__9);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__10 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems___closed__10);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabGenInjectiveTheorems_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
