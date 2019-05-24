// Lean compiler output
// Module: init.data.dlist
// Imports: init.data.list.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_DList_append(obj*);
obj* l_DList_append___main(obj*);
obj* l_DList_cons___main(obj*);
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_DList_push(obj*);
obj* l_DList_toList___rarg(obj*);
obj* l_DList_HasAppend___closed__1;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_DList_HasEmptyc(obj*);
obj* l_DList_cons___rarg(obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_DList_singleton(obj*);
obj* l_DList_toList(obj*);
obj* l_DList_append___rarg(obj*, obj*);
obj* l_DList_toList___main(obj*);
obj* l_DList_cons___main___elambda__1___rarg(obj*, obj*, obj*);
obj* l_DList_cons___main___rarg(obj*, obj*);
obj* l_DList_HasAppend(obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_DList_cons(obj*);
obj* l_DList_toList___main___rarg(obj*);
obj* l_DList_append___main___rarg(obj*, obj*);
obj* l_DList_empty(obj*);
obj* l_DList_push___rarg(obj*, obj*);
obj* l_DList_push___main___elambda__1___rarg(obj*, obj*, obj*);
obj* l_DList_singleton___rarg(obj*);
obj* l_DList_empty___closed__1;
obj* l_DList_push___main___elambda__1(obj*);
obj* l_DList_push___main___rarg(obj*, obj*);
obj* l_DList_cons___main___elambda__1(obj*);
obj* l_DList_push___main(obj*);
obj* l_DList_ofList(obj*);
obj* l_DList_singleton___elambda__1(obj*);
obj* l_DList_ofList___rarg(obj*);
obj* l_DList_ofList___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_append___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_DList_ofList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_ofList___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_DList_empty___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_DList_empty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DList_empty___closed__1;
return x_2;
}
}
obj* l_DList_HasEmptyc(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DList_empty___closed__1;
return x_2;
}
}
obj* l_DList_toList___main___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_DList_toList___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_toList___main___rarg), 1, 0);
return x_2;
}
}
obj* l_DList_toList___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DList_toList___main___rarg(x_1);
return x_2;
}
}
obj* l_DList_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_toList___rarg), 1, 0);
return x_2;
}
}
obj* l_DList_singleton___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_DList_singleton___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* l_DList_singleton___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_DList_singleton(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 1, 0);
return x_2;
}
}
obj* l_DList_cons___main___elambda__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_DList_cons___main___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_cons___main___elambda__1___rarg), 3, 0);
return x_2;
}
}
obj* l_DList_cons___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_cons___main___elambda__1___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_DList_cons___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_cons___main___rarg), 2, 0);
return x_2;
}
}
obj* l_DList_cons___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_cons___main___elambda__1___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_DList_cons(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_cons___rarg), 2, 0);
return x_2;
}
}
obj* l_DList_append___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_DList_append___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_append___main___rarg), 2, 0);
return x_2;
}
}
obj* l_DList_append___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_DList_append(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_append___rarg), 2, 0);
return x_2;
}
}
obj* l_DList_push___main___elambda__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_DList_push___main___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_push___main___elambda__1___rarg), 3, 0);
return x_2;
}
}
obj* l_DList_push___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_push___main___elambda__1___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_DList_push___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_push___main___rarg), 2, 0);
return x_2;
}
}
obj* l_DList_push___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_push___main___elambda__1___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_DList_push(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_push___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_DList_HasAppend___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_append___rarg), 2, 0);
return x_1;
}
}
obj* l_DList_HasAppend(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DList_HasAppend___closed__1;
return x_2;
}
}
obj* initialize_init_data_list_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_dlist(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
l_DList_empty___closed__1 = _init_l_DList_empty___closed__1();
lean::mark_persistent(l_DList_empty___closed__1);
l_DList_HasAppend___closed__1 = _init_l_DList_HasAppend___closed__1();
lean::mark_persistent(l_DList_HasAppend___closed__1);
return w;
}
