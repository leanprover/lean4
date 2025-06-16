// Lean compiler output
// Module: Lake.Build.Target.Basic
// Imports: Lake.Build.Key
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
LEAN_EXPORT lean_object* l_Lake_Target_repr___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_instReprTarget___closed__1;
static lean_object* l_Lake_Target_repr___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___rarg(lean_object*);
static lean_object* l_Lake_Target_repr___rarg___closed__2;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringTarget___rarg(lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
static lean_object* l_Lake_Target_repr___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Target_repr(lean_object*);
lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget(lean_object*);
static lean_object* l_Lake_Target_repr___rarg___closed__1;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprTarget(lean_object*);
static lean_object* l_Lake_Target_repr___rarg___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___rarg___boxed(lean_object*);
static lean_object* _init_l_Lake_Target_repr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Target.mk", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_repr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Target_repr___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Target_repr___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Target_repr___rarg___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Target_repr___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Target_repr___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
x_5 = l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(x_1, x_3);
x_6 = l_Lake_Target_repr___rarg___closed__3;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
if (x_4 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_Target_repr___rarg___closed__4;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lake_Target_repr___rarg___closed__5;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = 0;
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = l_Repr_addAppParen(x_16, x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Target_repr___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Target_repr___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Target_repr___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instReprTarget___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringTarget___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PartialBuildKey_toString(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToStringTarget___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instCoePartialBuildKeyTarget___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoePartialBuildKeyTarget___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lake_Build_Key(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Target_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Key(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Target_repr___rarg___closed__1 = _init_l_Lake_Target_repr___rarg___closed__1();
lean_mark_persistent(l_Lake_Target_repr___rarg___closed__1);
l_Lake_Target_repr___rarg___closed__2 = _init_l_Lake_Target_repr___rarg___closed__2();
lean_mark_persistent(l_Lake_Target_repr___rarg___closed__2);
l_Lake_Target_repr___rarg___closed__3 = _init_l_Lake_Target_repr___rarg___closed__3();
lean_mark_persistent(l_Lake_Target_repr___rarg___closed__3);
l_Lake_Target_repr___rarg___closed__4 = _init_l_Lake_Target_repr___rarg___closed__4();
lean_mark_persistent(l_Lake_Target_repr___rarg___closed__4);
l_Lake_Target_repr___rarg___closed__5 = _init_l_Lake_Target_repr___rarg___closed__5();
lean_mark_persistent(l_Lake_Target_repr___rarg___closed__5);
l_Lake_instReprTarget___closed__1 = _init_l_Lake_instReprTarget___closed__1();
lean_mark_persistent(l_Lake_instReprTarget___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
