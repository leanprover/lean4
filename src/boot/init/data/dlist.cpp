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
#endif
obj* _l_s5_dlist_s8_of__list(obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_dlist_s4_push(obj*);
obj* _l_s5_dlist_s6_append(obj*);
obj* _l_s5_dlist_s4_cons_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_dlist_s8_of__list_s6___rarg(obj*);
obj* _l_s5_dlist_s4_push_s6___rarg(obj*, obj*);
obj* _l_s5_dlist_s4_cons_s6___main(obj*);
obj* _l_s5_dlist_s6_append_s6___main(obj*);
obj* _l_s2_id_s6___rarg(obj*);
obj* _l_s5_dlist_s11_has__append(obj*);
obj* _l_s5_dlist_s6_append_s6___main_s6___rarg(obj*, obj*);
obj* _l_s5_dlist_s8_to__list(obj*);
obj* _l_s5_dlist_s9_singleton(obj*);
obj* _l_s5_dlist_s5_empty(obj*);
obj* _l_s5_dlist_s8_to__list_s6___main(obj*);
obj* _l_s5_dlist_s4_push_s6___main(obj*);
obj* _l_s5_dlist_s4_push_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s6_append_s6___rarg(obj*, obj*);
obj* _l_s5_dlist_s6_append_s6___rarg(obj*, obj*);
obj* _l_s5_dlist_s4_cons(obj*);
obj* _l_s5_dlist_s8_to__list_s6___rarg(obj*);
obj* _l_s5_dlist_s4_cons_s6___rarg(obj*, obj*);
obj* _l_s5_dlist_s8_to__list_s6___main_s6___rarg(obj*);
obj* _l_s5_dlist_s9_singleton_s6___rarg(obj*, obj*);
obj* _l_s5_dlist_s8_of__list_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_append_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s5_dlist_s8_of__list(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s8_of__list_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s5_dlist_s5_empty(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s5_dlist_s8_to__list_s6___main_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_cnstr(0, 0, 0);
;
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s5_dlist_s8_to__list_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s8_to__list_s6___main_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s5_dlist_s8_to__list_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s5_dlist_s8_to__list_s6___main_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s5_dlist_s8_to__list(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s8_to__list_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s5_dlist_s9_singleton_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_dlist_s9_singleton(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_dlist_s4_cons_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _l_s5_dlist_s4_cons_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s4_cons_s6___main_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_dlist_s4_cons_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s4_cons_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_dlist_s4_cons(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s4_cons_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_dlist_s6_append_s6___main_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_dlist_s6_append_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s6_append_s6___main_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_dlist_s6_append_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_dlist_s6_append(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s6_append_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_dlist_s4_push_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* _l_s5_dlist_s4_push_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s4_push_s6___main_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_dlist_s4_push_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s4_push_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_dlist_s4_push(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s4_push_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_dlist_s11_has__append(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s6_append_s6___rarg), 2, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
void _l_initialize__l_s4_init_s8_function();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s5_dlist() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
 _l_initialize__l_s4_init_s8_function();
}
