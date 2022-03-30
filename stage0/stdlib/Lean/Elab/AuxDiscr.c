// Lean compiler output
// Module: Lean.Elab.AuxDiscr
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
LEAN_EXPORT uint8_t l_Lean_isAuxDiscrName(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_isAuxFunDiscrName___boxed(lean_object*);
static lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__3;
static lean_object* l_Lean_mkAuxDiscr___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxDiscrName___boxed(lean_object*);
static lean_object* l_Lean_mkAuxDiscr___rarg___lambda__1___closed__2;
static lean_object* l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_isAuxFunDiscrName(lean_object*);
static lean_object* _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_discr");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4;
x_8 = l_Lean_addMacroScope(x_4, x_7, x_2);
x_9 = lean_box(0);
x_10 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__3;
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_mkAuxDiscr___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_mkAuxDiscr___rarg___lambda__2), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___rarg(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_mkAuxDiscr___rarg___lambda__3), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDiscr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkAuxDiscr___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_fun_discr");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4;
x_8 = l_Lean_addMacroScope(x_4, x_7, x_2);
x_9 = lean_box(0);
x_10 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__3;
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_mkAuxFunDiscr___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_mkAuxFunDiscr___rarg___lambda__2), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___rarg(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_mkAuxFunDiscr___rarg___lambda__3), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxFunDiscr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkAuxFunDiscr___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxDiscrName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_erase_macro_scopes(x_1);
x_5 = l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4;
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxDiscrName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isAuxDiscrName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxFunDiscrName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_erase_macro_scopes(x_1);
x_5 = l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4;
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxFunDiscrName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isAuxFunDiscrName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AuxDiscr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1 = _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_mkAuxDiscr___rarg___lambda__1___closed__1);
l_Lean_mkAuxDiscr___rarg___lambda__1___closed__2 = _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_mkAuxDiscr___rarg___lambda__1___closed__2);
l_Lean_mkAuxDiscr___rarg___lambda__1___closed__3 = _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_mkAuxDiscr___rarg___lambda__1___closed__3);
l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4 = _init_l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_mkAuxDiscr___rarg___lambda__1___closed__4);
l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1 = _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__1);
l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__2 = _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__2);
l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__3 = _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__3);
l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4 = _init_l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_mkAuxFunDiscr___rarg___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
