// Lean compiler output
// Module: Init.Data.Option.Instances
// Imports: Init.Data.Option.Basic
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
LEAN_EXPORT lean_object* l_Option_pfilter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pfilter(lean_object*);
LEAN_EXPORT lean_object* l_Option_forM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMembership(lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableExistsAndMemOfDecidablePred___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableForallForallMemOfDecidablePred___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidable__eq__none___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Option_decidable__eq__none(lean_object*);
LEAN_EXPORT lean_object* l_Option_instForM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pbind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq(lean_object*);
LEAN_EXPORT lean_object* l_Option_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidable__eq__none___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableForallForallMemOfDecidablePred(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembership___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableExistsAndMemOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pmap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembership___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pmap___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pbind___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMembership(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____rarg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_instDecidableMemOfDecidableEq___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Option_decidable__eq__none___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Option_decidable__eq__none(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_decidable__eq__none___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_decidable__eq__none___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Option_decidable__eq__none___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableForallForallMemOfDecidablePred___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = 1;
x_4 = lean_box(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableForallForallMemOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_instDecidableForallForallMemOfDecidablePred___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableExistsAndMemOfDecidablePred___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = 0;
x_4 = lean_box(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableExistsAndMemOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_instDecidableExistsAndMemOfDecidablePred___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_pbind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_4, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_pbind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_pbind___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_pmap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_apply_2(x_1, x_6, lean_box(0));
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_1, x_8, lean_box(0));
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Option_pmap___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_pelim___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_3, x_4, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_pelim___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_pelim___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_pelim___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_pfilter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_apply_2(x_2, x_4, lean_box(0));
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pfilter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_pfilter___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Option_forM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_forM___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_instForM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_instForM___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembership___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembership___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_apply_3(x_4, x_8, lean_box(0), x_3);
x_11 = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembership___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembership(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembership___rarg), 4, 0);
return x_4;
}
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
