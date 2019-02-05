// Lean compiler output
// Module: init.data.dlist
// Imports: init.data.list.basic init.function
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_dlist_of__list(obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_dlist_push(obj*);
obj* l_dlist_append(obj*);
obj* l_dlist_cons___main___rarg(obj*, obj*, obj*);
obj* l_dlist_of__list___rarg(obj*);
obj* l_dlist_push___rarg(obj*, obj*);
obj* l_dlist_cons___main(obj*);
obj* l_dlist_append___main(obj*);
obj* l_id___rarg(obj*);
obj* l_dlist_has__append(obj*);
obj* l_dlist_append___main___rarg(obj*, obj*);
obj* l_dlist_to__list(obj*);
obj* l_dlist_singleton(obj*);
obj* l_dlist_empty(obj*);
obj* l_dlist_to__list___main(obj*);
obj* l_dlist_push___main(obj*);
obj* l_dlist_push___main___rarg(obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_dlist_append___rarg(obj*, obj*);
obj* l_dlist_cons(obj*);
obj* l_dlist_to__list___rarg(obj*);
obj* l_dlist_cons___rarg(obj*, obj*);
obj* l_dlist_to__list___main___rarg(obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_dlist_of__list___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_append___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_dlist_of__list(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_of__list___rarg), 1, 0);
return x_2;
}
}
obj* l_dlist_empty(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
return x_2;
}
}
obj* l_dlist_to__list___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_dlist_to__list___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_to__list___main___rarg), 1, 0);
return x_2;
}
}
obj* l_dlist_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_dlist_to__list___main___rarg(x_0);
return x_1;
}
}
obj* l_dlist_to__list(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_to__list___rarg), 1, 0);
return x_2;
}
}
obj* l_dlist_singleton___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_dlist_singleton(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 0);
return x_2;
}
}
obj* l_dlist_cons___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_dlist_cons___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_cons___main___rarg), 3, 0);
return x_2;
}
}
obj* l_dlist_cons___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_cons___main___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_dlist_cons(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_cons___rarg), 2, 0);
return x_2;
}
}
obj* l_dlist_append___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_dlist_append___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_append___main___rarg), 2, 0);
return x_2;
}
}
obj* l_dlist_append___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_dlist_append(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_append___rarg), 2, 0);
return x_2;
}
}
obj* l_dlist_push___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* l_dlist_push___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_push___main___rarg), 3, 0);
return x_2;
}
}
obj* l_dlist_push___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_push___main___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_dlist_push(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_push___rarg), 2, 0);
return x_2;
}
}
obj* l_dlist_has__append(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_append___rarg), 2, 0);
return x_2;
}
}
void initialize_init_data_list_basic();
void initialize_init_function();
static bool _G_initialized = false;
void initialize_init_data_dlist() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_list_basic();
 initialize_init_function();
}
