// Lean compiler output
// Module: Init.Data.Sum
// Imports: Init.Core Init.Util
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
LEAN_EXPORT lean_object* l_Sum_getLeft_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_isRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getRight_x3f(lean_object*, lean_object*);
static lean_object* l_Sum_getLeft_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Sum_getRight___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_decEqSum____x40_Init_Data_Sum___hyg_4____rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getRight_x3f___rarg(lean_object*);
static lean_object* l_Sum_getRight_x21___rarg___closed__1;
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getRight_x21___rarg(lean_object*, lean_object*);
static lean_object* l_Sum_getLeft_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Sum_getRight_x21(lean_object*, lean_object*);
static lean_object* l_Sum_getLeft_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_decEqSum____x40_Init_Data_Sum___hyg_4_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_isLeft___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Sum_getRight(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft_x3f___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Sum_isLeft___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Sum_lift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_isRight___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Sum_getRight_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_lift___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_beqSum____x40_Init_Data_Sum___hyg_242_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_isLeft(lean_object*, lean_object*);
static lean_object* l_Sum_getRight_x21___rarg___closed__2;
static lean_object* l_Sum_getRight_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_beqSum____x40_Init_Data_Sum___hyg_242____rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_instBEq(lean_object*, lean_object*);
static lean_object* l_Sum_getLeft_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Sum_instBEq___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Sum_isRight___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Sum_instDecidableEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getRight___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_getLeft___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_decEqSum____x40_Init_Data_Sum___hyg_4____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = 0;
x_11 = lean_box(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_decEqSum____x40_Init_Data_Sum___hyg_4_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Sum_0__Sum_decEqSum____x40_Init_Data_Sum___hyg_4____rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_instDecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Sum_0__Sum_decEqSum____x40_Init_Data_Sum___hyg_4____rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Sum_instDecidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_instDecidableEq___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_beqSum____x40_Init_Data_Sum___hyg_242____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = 0;
x_11 = lean_box(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_0__Sum_beqSum____x40_Init_Data_Sum___hyg_242_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Sum_0__Sum_beqSum____x40_Init_Data_Sum___hyg_242____rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_instBEq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Sum_0__Sum_beqSum____x40_Init_Data_Sum___hyg_242____rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_instBEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_instBEq___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Sum_isLeft___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Sum_isLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_isLeft___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_isLeft___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Sum_isLeft___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Sum_isRight___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Sum_isRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_isRight___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_isRight___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Sum_isRight___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_getLeft___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Sum_getLeft___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getRight___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_getRight___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getRight___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Sum_getRight___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_getLeft_x3f___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getRight_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Sum_getRight_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_getRight_x3f___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Sum_getLeft_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Sum", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Sum_getLeft_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sum.getLeft!", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Sum_getLeft_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is inr", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Sum_getLeft_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Sum_getLeft_x21___rarg___closed__1;
x_2 = l_Sum_getLeft_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(45u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Sum_getLeft_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Sum_getLeft_x21___rarg___closed__4;
x_5 = l_panic___rarg(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_getLeft_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getLeft_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Sum_getLeft_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Sum_getRight_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sum.getRight!", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Sum_getRight_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is inl", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Sum_getRight_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Sum_getLeft_x21___rarg___closed__1;
x_2 = l_Sum_getRight_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(48u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Sum_getRight_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Sum_getRight_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Sum_getRight_x21___rarg___closed__3;
x_4 = l_panic___rarg(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Sum_getRight_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_getRight_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_getRight_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Sum_getRight_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_lift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Sum_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Sum_lift___rarg), 3, 0);
return x_4;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Sum(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Sum_getLeft_x21___rarg___closed__1 = _init_l_Sum_getLeft_x21___rarg___closed__1();
lean_mark_persistent(l_Sum_getLeft_x21___rarg___closed__1);
l_Sum_getLeft_x21___rarg___closed__2 = _init_l_Sum_getLeft_x21___rarg___closed__2();
lean_mark_persistent(l_Sum_getLeft_x21___rarg___closed__2);
l_Sum_getLeft_x21___rarg___closed__3 = _init_l_Sum_getLeft_x21___rarg___closed__3();
lean_mark_persistent(l_Sum_getLeft_x21___rarg___closed__3);
l_Sum_getLeft_x21___rarg___closed__4 = _init_l_Sum_getLeft_x21___rarg___closed__4();
lean_mark_persistent(l_Sum_getLeft_x21___rarg___closed__4);
l_Sum_getRight_x21___rarg___closed__1 = _init_l_Sum_getRight_x21___rarg___closed__1();
lean_mark_persistent(l_Sum_getRight_x21___rarg___closed__1);
l_Sum_getRight_x21___rarg___closed__2 = _init_l_Sum_getRight_x21___rarg___closed__2();
lean_mark_persistent(l_Sum_getRight_x21___rarg___closed__2);
l_Sum_getRight_x21___rarg___closed__3 = _init_l_Sum_getRight_x21___rarg___closed__3();
lean_mark_persistent(l_Sum_getRight_x21___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
