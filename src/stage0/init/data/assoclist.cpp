// Lean compiler output
// Module: init.data.assoclist
// Imports: init.control.id
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
obj* l_AssocList_foldl___rarg(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_AssocList_foldl___spec__1(obj*, obj*, obj*);
obj* l_AssocList_replace___main(obj*, obj*);
obj* l_AssocList_erase___rarg(obj*, obj*, obj*);
obj* l_AssocList_find___main(obj*, obj*);
obj* l_AssocList_mfoldl(obj*, obj*, obj*, obj*);
obj* l_AssocList_erase___main___rarg(obj*, obj*, obj*);
obj* l_AssocList_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_contains(obj*, obj*);
obj* l_AssocList_find___rarg(obj*, obj*, obj*);
obj* l_AssocList_find___main___rarg(obj*, obj*, obj*);
uint8 l_AssocList_contains___rarg(obj*, obj*, obj*);
obj* l_AssocList_contains___main___rarg___boxed(obj*, obj*, obj*);
uint8 l_AssocList_contains___main___rarg(obj*, obj*, obj*);
obj* l_AssocList_foldl(obj*, obj*, obj*);
obj* l_AssocList_replace___main___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_replace(obj*, obj*);
obj* l_AssocList_mfoldl___main(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_AssocList_foldl___spec__1___rarg(obj*, obj*, obj*);
obj* l_AssocList_erase(obj*, obj*);
obj* l_AssocList_find(obj*, obj*);
obj* l_AssocList_mfoldl___main___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_erase___main(obj*, obj*);
obj* l_AssocList_replace___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_contains___main(obj*, obj*);
obj* l_AssocList_mfoldl___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_AssocList_mfoldl___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_AssocList_mfoldl___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 2);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_2);
x_12 = lean::apply_3(x_2, x_3, x_8, x_9);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___rarg___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_10);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
}
obj* l_AssocList_mfoldl___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___rarg), 4, 0);
return x_5;
}
}
obj* l_AssocList_mfoldl___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_AssocList_mfoldl___main(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_AssocList_mfoldl___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_AssocList_mfoldl___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_AssocList_mfoldl(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___rarg), 4, 0);
return x_5;
}
}
obj* l_AssocList_mfoldl___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_AssocList_mfoldl(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_AssocList_mfoldl___main___at_AssocList_foldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
obj* l_AssocList_mfoldl___main___at_AssocList_foldl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___at_AssocList_foldl___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_AssocList_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_AssocList_mfoldl___main___at_AssocList_foldl___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_AssocList_foldl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_foldl___rarg), 3, 0);
return x_4;
}
}
obj* l_AssocList_find___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 2);
lean::inc(x_7);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_2);
x_8 = lean::apply_2(x_1, x_5, x_2);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_6);
x_3 = x_7;
goto _start;
}
else
{
obj* x_11; 
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_6);
return x_11;
}
}
}
}
obj* l_AssocList_find___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_find___main___rarg), 3, 0);
return x_3;
}
}
obj* l_AssocList_find___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_AssocList_find___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_AssocList_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_find___rarg), 3, 0);
return x_3;
}
}
uint8 l_AssocList_contains___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = 0;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_2);
x_7 = lean::apply_2(x_1, x_5, x_2);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
uint8 x_10; 
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_10 = 1;
return x_10;
}
}
}
}
obj* l_AssocList_contains___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_contains___main___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_AssocList_contains___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_AssocList_contains___main___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_AssocList_contains___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_AssocList_contains___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_AssocList_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_contains___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_AssocList_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_AssocList_contains___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_AssocList_replace___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean::cnstr_get(x_4, 2);
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_6);
x_9 = lean::apply_2(x_1, x_6, x_2);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; 
x_11 = l_AssocList_replace___main___rarg(x_1, x_2, x_3, x_8);
lean::cnstr_set(x_4, 2, x_11);
return x_4;
}
else
{
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 0, x_2);
return x_4;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_12 = lean::cnstr_get(x_4, 0);
x_13 = lean::cnstr_get(x_4, 1);
x_14 = lean::cnstr_get(x_4, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_12);
x_15 = lean::apply_2(x_1, x_12, x_2);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = l_AssocList_replace___main___rarg(x_1, x_2, x_3, x_14);
x_18 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_13);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_1);
x_19 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_3);
lean::cnstr_set(x_19, 2, x_14);
return x_19;
}
}
}
}
}
obj* l_AssocList_replace___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_replace___main___rarg), 4, 0);
return x_3;
}
}
obj* l_AssocList_replace___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_AssocList_replace___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_AssocList_replace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_replace___rarg), 4, 0);
return x_3;
}
}
obj* l_AssocList_erase___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 2);
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_5);
x_8 = lean::apply_2(x_1, x_5, x_2);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
x_10 = l_AssocList_erase___main___rarg(x_1, x_2, x_7);
lean::cnstr_set(x_3, 2, x_10);
return x_3;
}
else
{
lean::free_heap_obj(x_3);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_11);
x_14 = lean::apply_2(x_1, x_11, x_2);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_AssocList_erase___main___rarg(x_1, x_2, x_13);
x_17 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_12);
lean::cnstr_set(x_17, 2, x_16);
return x_17;
}
else
{
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_1);
return x_13;
}
}
}
}
}
obj* l_AssocList_erase___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_erase___main___rarg), 3, 0);
return x_3;
}
}
obj* l_AssocList_erase___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_AssocList_erase___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_AssocList_erase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_erase___rarg), 3, 0);
return x_3;
}
}
obj* initialize_init_control_id(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_assoclist(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_id(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
