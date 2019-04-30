// Lean compiler output
// Module: init.data.assoclist
// Imports: init.core
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
obj* l_AssocList_foldl___main___boxed(obj*, obj*, obj*);
obj* l_AssocList_foldl___rarg(obj*, obj*, obj*);
obj* l_AssocList_erase___main___boxed(obj*, obj*);
obj* l_AssocList_replace___main(obj*, obj*);
obj* l_AssocList_erase___rarg(obj*, obj*, obj*);
obj* l_AssocList_find___main(obj*, obj*);
obj* l_AssocList_find___main___boxed(obj*, obj*);
obj* l_AssocList_contains___main___boxed(obj*, obj*);
obj* l_AssocList_erase___main___rarg(obj*, obj*, obj*);
obj* l_AssocList_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_AssocList_contains(obj*, obj*);
obj* l_AssocList_find___rarg(obj*, obj*, obj*);
obj* l_AssocList_find___main___rarg(obj*, obj*, obj*);
obj* l_AssocList_erase___boxed(obj*, obj*);
uint8 l_AssocList_contains___rarg(obj*, obj*, obj*);
obj* l_AssocList_contains___main___rarg___boxed(obj*, obj*, obj*);
uint8 l_AssocList_contains___main___rarg(obj*, obj*, obj*);
obj* l_AssocList_foldl___boxed(obj*, obj*, obj*);
obj* l_AssocList_find___boxed(obj*, obj*);
obj* l_AssocList_foldl(obj*, obj*, obj*);
obj* l_AssocList_replace___main___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_replace(obj*, obj*);
obj* l_AssocList_erase(obj*, obj*);
obj* l_AssocList_find(obj*, obj*);
obj* l_AssocList_erase___main(obj*, obj*);
obj* l_AssocList_replace___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_replace___boxed(obj*, obj*);
obj* l_AssocList_contains___boxed(obj*, obj*);
obj* l_AssocList_contains___main(obj*, obj*);
obj* l_AssocList_replace___main___boxed(obj*, obj*);
obj* l_AssocList_foldl___main(obj*, obj*, obj*);
obj* l_AssocList_foldl___main___rarg(obj*, obj*, obj*);
obj* l_AssocList_foldl___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 2);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_0);
x_12 = lean::apply_3(x_0, x_1, x_4, x_6);
x_1 = x_12;
x_2 = x_8;
goto _start;
}
}
}
obj* l_AssocList_foldl___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_foldl___main___rarg), 3, 0);
return x_3;
}
}
obj* l_AssocList_foldl___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_foldl___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_AssocList_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_foldl___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_AssocList_foldl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_foldl___rarg), 3, 0);
return x_3;
}
}
obj* l_AssocList_foldl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_foldl(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_AssocList_find___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 2);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_6, x_1);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
lean::dec(x_8);
x_2 = x_10;
goto _start;
}
else
{
obj* x_22; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_8);
return x_22;
}
}
}
}
obj* l_AssocList_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_find___main___rarg), 3, 0);
return x_2;
}
}
obj* l_AssocList_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_AssocList_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_find___rarg), 3, 0);
return x_2;
}
}
obj* l_AssocList_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_AssocList_contains___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = 0;
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_13; uint8 x_14; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 2);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_6, x_1);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
uint8 x_19; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_8);
x_19 = 1;
return x_19;
}
}
}
}
obj* l_AssocList_contains___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_contains___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_AssocList_contains___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_AssocList_contains___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_contains___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_AssocList_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_AssocList_contains___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_AssocList_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_contains___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_AssocList_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_AssocList_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_replace___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_17; uint8 x_18; 
x_7 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
x_11 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 x_13 = x_3;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_3);
 x_13 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_7);
lean::inc(x_0);
x_17 = lean::apply_2(x_0, x_7, x_1);
x_18 = lean::unbox(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = l_AssocList_replace___main___rarg(x_0, x_1, x_2, x_11);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_19);
return x_20;
}
else
{
obj* x_24; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_9);
if (lean::is_scalar(x_13)) {
 x_24 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_24 = x_13;
}
lean::cnstr_set(x_24, 0, x_1);
lean::cnstr_set(x_24, 1, x_2);
lean::cnstr_set(x_24, 2, x_11);
return x_24;
}
}
}
}
obj* l_AssocList_replace___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_replace___main___rarg), 4, 0);
return x_2;
}
}
obj* l_AssocList_replace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_replace___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_replace___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_AssocList_replace___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_AssocList_replace(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_replace___rarg), 4, 0);
return x_2;
}
}
obj* l_AssocList_replace___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_replace(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_erase___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; uint8 x_16; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_5, x_1);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = l_AssocList_erase___main___rarg(x_0, x_1, x_9);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_7);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_11);
return x_9;
}
}
}
}
obj* l_AssocList_erase___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_erase___main___rarg), 3, 0);
return x_2;
}
}
obj* l_AssocList_erase___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_erase___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_erase___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_erase___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_AssocList_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_erase___rarg), 3, 0);
return x_2;
}
}
obj* l_AssocList_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_core(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_assoclist(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
return w;
}
