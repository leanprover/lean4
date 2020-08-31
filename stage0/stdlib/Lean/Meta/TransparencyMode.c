// Lean compiler output
// Module: Lean.Meta.TransparencyMode
// Imports: Init
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
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l_Lean_Meta_TransparencyMode_Hashable___closed__1;
lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_Hashable;
uint8_t l_Lean_Meta_TransparencyMode_Inhabited;
lean_object* l_Lean_Meta_TransparencyMode_HasBeq___closed__1;
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_TransparencyMode_HasBeq;
lean_object* l_Lean_Meta_TransparencyMode_beq___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object*);
uint8_t _init_l_Lean_Meta_TransparencyMode_Inhabited() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_TransparencyMode_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_TransparencyMode_HasBeq___closed__1;
return x_1;
}
}
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
size_t x_2; 
x_2 = 7;
return x_2;
}
case 1:
{
size_t x_3; 
x_3 = 11;
return x_3;
}
default: 
{
size_t x_4; 
x_4 = 13;
return x_4;
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_TransparencyMode_Hashable___closed__1;
return x_1;
}
}
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_box(x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
default: 
{
lean_object* x_7; 
x_7 = lean_box(x_2);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_TransparencyMode_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_TransparencyMode(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_TransparencyMode_Inhabited = _init_l_Lean_Meta_TransparencyMode_Inhabited();
l_Lean_Meta_TransparencyMode_HasBeq___closed__1 = _init_l_Lean_Meta_TransparencyMode_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_HasBeq___closed__1);
l_Lean_Meta_TransparencyMode_HasBeq = _init_l_Lean_Meta_TransparencyMode_HasBeq();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_HasBeq);
l_Lean_Meta_TransparencyMode_Hashable___closed__1 = _init_l_Lean_Meta_TransparencyMode_Hashable___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_Hashable___closed__1);
l_Lean_Meta_TransparencyMode_Hashable = _init_l_Lean_Meta_TransparencyMode_Hashable();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_Hashable);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
