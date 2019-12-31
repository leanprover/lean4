// Lean compiler output
// Module: Init.Lean.AuxRecursor
// Imports: Init.Lean.Environment
#include "runtime/lean.h"
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
lean_object* l_Lean_noConfusionExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* lean_mark_aux_recursor(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_noConfusionExt___elambda__2___boxed(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_noConfusionExt___closed__5;
lean_object* l_Lean_auxRecExt___elambda__1___boxed(lean_object*);
lean_object* l_Lean_noConfusionExt___closed__3;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_auxRecExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_auxRecExt___closed__4;
lean_object* l_Lean_noConfusionExt___closed__1;
lean_object* l_Lean_auxRecExt___closed__1;
lean_object* l_Lean_auxRecExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_isNoConfusion___boxed(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___closed__2;
lean_object* l_Lean_auxRecExt___closed__2;
lean_object* l_Lean_mkAuxRecursorExtension___closed__1;
lean_object* lean_mark_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_mkAuxRecursorExtension(lean_object*);
lean_object* l_Lean_mkAuxRecursorExtension___closed__2;
lean_object* l_Lean_noConfusionExt___closed__4;
lean_object* l_Lean_auxRecExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_mkNoConfusionExtension___closed__1;
lean_object* l_Lean_noConfusionExt___elambda__1___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_auxRecExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_auxRecExt___closed__5;
lean_object* l_Lean_mkNoConfusionExtension___closed__2;
lean_object* l_Lean_auxRecExt___closed__3;
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__1(lean_object*);
lean_object* l_Lean_auxRecExt___elambda__3___boxed(lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__2(lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_mkNoConfusionExtension(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_namespacesExt___closed__1;
lean_object* l_Lean_isAuxRecursor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__2(lean_object*);
lean_object* _init_l_Lean_mkAuxRecursorExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("auxRec");
return x_1;
}
}
lean_object* _init_l_Lean_mkAuxRecursorExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAuxRecursorExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkAuxRecursorExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkAuxRecursorExtension___closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_auxRecExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_auxRecExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_auxRecExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_Lean_auxRecExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_auxRecExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_auxRecExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_auxRecExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_auxRecExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_namespacesExt___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_auxRecExt___closed__1;
x_4 = l_Lean_auxRecExt___closed__2;
x_5 = l_Lean_auxRecExt___closed__3;
x_6 = l_Lean_auxRecExt___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_auxRecExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_auxRecExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_auxRecExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_auxRecExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_auxRecExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_auxRecExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_mark_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_auxRecExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t lean_is_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_auxRecExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_isAuxRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_aux_recursor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_mkNoConfusionExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noConf");
return x_1;
}
}
lean_object* _init_l_Lean_mkNoConfusionExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNoConfusionExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkNoConfusionExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkNoConfusionExtension___closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_noConfusionExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_noConfusionExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_noConfusionExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_Lean_noConfusionExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_noConfusionExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_noConfusionExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_noConfusionExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_noConfusionExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_namespacesExt___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_noConfusionExt___closed__1;
x_4 = l_Lean_noConfusionExt___closed__2;
x_5 = l_Lean_noConfusionExt___closed__3;
x_6 = l_Lean_noConfusionExt___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_noConfusionExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_noConfusionExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_noConfusionExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_noConfusionExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_noConfusionExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_noConfusionExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_mark_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_noConfusionExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t lean_is_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_noConfusionExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_isNoConfusion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_no_confusion(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_AuxRecursor(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkAuxRecursorExtension___closed__1 = _init_l_Lean_mkAuxRecursorExtension___closed__1();
lean_mark_persistent(l_Lean_mkAuxRecursorExtension___closed__1);
l_Lean_mkAuxRecursorExtension___closed__2 = _init_l_Lean_mkAuxRecursorExtension___closed__2();
lean_mark_persistent(l_Lean_mkAuxRecursorExtension___closed__2);
l_Lean_auxRecExt___closed__1 = _init_l_Lean_auxRecExt___closed__1();
lean_mark_persistent(l_Lean_auxRecExt___closed__1);
l_Lean_auxRecExt___closed__2 = _init_l_Lean_auxRecExt___closed__2();
lean_mark_persistent(l_Lean_auxRecExt___closed__2);
l_Lean_auxRecExt___closed__3 = _init_l_Lean_auxRecExt___closed__3();
lean_mark_persistent(l_Lean_auxRecExt___closed__3);
l_Lean_auxRecExt___closed__4 = _init_l_Lean_auxRecExt___closed__4();
lean_mark_persistent(l_Lean_auxRecExt___closed__4);
l_Lean_auxRecExt___closed__5 = _init_l_Lean_auxRecExt___closed__5();
lean_mark_persistent(l_Lean_auxRecExt___closed__5);
res = l_Lean_mkAuxRecursorExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_auxRecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxRecExt);
lean_dec_ref(res);
l_Lean_mkNoConfusionExtension___closed__1 = _init_l_Lean_mkNoConfusionExtension___closed__1();
lean_mark_persistent(l_Lean_mkNoConfusionExtension___closed__1);
l_Lean_mkNoConfusionExtension___closed__2 = _init_l_Lean_mkNoConfusionExtension___closed__2();
lean_mark_persistent(l_Lean_mkNoConfusionExtension___closed__2);
l_Lean_noConfusionExt___closed__1 = _init_l_Lean_noConfusionExt___closed__1();
lean_mark_persistent(l_Lean_noConfusionExt___closed__1);
l_Lean_noConfusionExt___closed__2 = _init_l_Lean_noConfusionExt___closed__2();
lean_mark_persistent(l_Lean_noConfusionExt___closed__2);
l_Lean_noConfusionExt___closed__3 = _init_l_Lean_noConfusionExt___closed__3();
lean_mark_persistent(l_Lean_noConfusionExt___closed__3);
l_Lean_noConfusionExt___closed__4 = _init_l_Lean_noConfusionExt___closed__4();
lean_mark_persistent(l_Lean_noConfusionExt___closed__4);
l_Lean_noConfusionExt___closed__5 = _init_l_Lean_noConfusionExt___closed__5();
lean_mark_persistent(l_Lean_noConfusionExt___closed__5);
res = l_Lean_mkNoConfusionExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_noConfusionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noConfusionExt);
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
