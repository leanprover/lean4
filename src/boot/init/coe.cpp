// Lean compiler output
// Module: init.coe
// Imports: init.data.list.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_coe___rarg(obj*, obj*);
obj* l_coe(obj*, obj*);
obj* l_coe__sort__bool;
obj* l_lift__fn__range___rarg(obj*, obj*, obj*);
obj* l_coe__trans___rarg(obj*, obj*, obj*);
obj* l_lift__fn__range(obj*, obj*, obj*);
obj* l_coe__subtype___rarg(obj*);
obj* l_coe__b___rarg(obj*, obj*);
obj* l_coe__to__lift(obj*, obj*);
obj* l_list_map___main___at_lift__list___spec__1___rarg(obj*, obj*);
obj* l_coe__trans__aux(obj*, obj*, obj*);
obj* l_coe__option___rarg(obj*);
obj* l_coe__trans(obj*, obj*, obj*);
obj* l_coe__fn__trans(obj*, obj*);
obj* l_lift__list(obj*, obj*);
obj* l_lift__pair_u_2082(obj*, obj*, obj*);
obj* l_coe__sort(obj*);
obj* l_coe__option(obj*);
obj* l_lift__t___rarg(obj*, obj*);
uint8 l_coe__decidable__eq(uint8);
obj* l_coe__t___rarg(obj*, obj*);
obj* l_lift__refl(obj*);
obj* l_lift__list___rarg(obj*, obj*);
obj* l_list_map___main___at_lift__list___spec__1(obj*, obj*);
obj* l_lift__pair_u_2081___rarg(obj*, obj*);
obj* l_coe__to__lift___rarg(obj*);
obj* l_lift__fn__dom___rarg(obj*, obj*, obj*);
obj* l_lift__pair___rarg(obj*, obj*, obj*);
obj* l_coe__fn__b___rarg(obj*, obj*);
obj* l_coe__decidable__eq___boxed(obj*);
obj* l_lift___rarg(obj*, obj*);
obj* l_coe__b(obj*, obj*);
obj* l_coe__subtype(obj*, obj*);
obj* l_coe__fn__b(obj*);
obj* l_coe__sort__trans___rarg(obj*, obj*, obj*);
obj* l_coe__base__aux___rarg(obj*);
obj* l_id___rarg(obj*);
obj* l_coe__bool__to__Prop;
obj* l_lift__fn__dom(obj*, obj*, obj*);
obj* l_lift__pair(obj*, obj*, obj*, obj*);
obj* l_lift__t(obj*, obj*);
obj* l_lift__fn___rarg(obj*, obj*, obj*, obj*);
obj* l_coe__trans__aux___rarg(obj*, obj*, obj*);
obj* l_lift__fn(obj*, obj*, obj*, obj*);
obj* l_lift__pair_u_2081(obj*, obj*, obj*);
obj* l_coe__fn__trans___rarg(obj*, obj*, obj*);
obj* l_coe__fn___rarg(obj*, obj*);
obj* l_coe__fn(obj*);
obj* l_coe__base(obj*, obj*);
obj* l_coe__t(obj*, obj*);
obj* l_lift__trans(obj*, obj*, obj*);
obj* l_coe__sort___rarg(obj*, obj*);
obj* l_coe__base__aux(obj*, obj*);
obj* l_lift__pair_u_2082___rarg(obj*, obj*);
obj* l_coe__base___rarg(obj*);
obj* l_coe__sort__trans(obj*, obj*);
obj* l_lift(obj*, obj*);
obj* l_lift__trans___rarg(obj*, obj*, obj*);
obj* l_lift___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lift___rarg), 2, 0);
return x_4;
}
}
obj* l_lift__t___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_lift__t(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__t___rarg), 2, 0);
return x_4;
}
}
obj* l_coe__b___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe__b(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__b___rarg), 2, 0);
return x_4;
}
}
obj* l_coe__t___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe__t(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__t___rarg), 2, 0);
return x_4;
}
}
obj* l_coe__fn__b___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe__fn__b(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__fn__b___rarg), 2, 0);
return x_2;
}
}
obj* l_coe___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___rarg), 2, 0);
return x_4;
}
}
obj* l_coe__fn___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe__fn(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__fn___rarg), 2, 0);
return x_2;
}
}
obj* l_coe__sort___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe__sort(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__sort___rarg), 2, 0);
return x_2;
}
}
obj* l_lift__trans___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_lift__trans(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__trans___rarg), 3, 0);
return x_6;
}
}
obj* l_lift__refl(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
return x_2;
}
}
obj* l_coe__trans___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_coe__trans(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__trans___rarg), 3, 0);
return x_6;
}
}
obj* l_coe__base___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__b___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe__base(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__base___rarg), 1, 0);
return x_4;
}
}
obj* l_coe__option___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe__option(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__option___rarg), 1, 0);
return x_2;
}
}
obj* l_coe__trans__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_coe__trans__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__trans__aux___rarg), 3, 0);
return x_6;
}
}
obj* l_coe__base__aux___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__b___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe__base__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__base__aux___rarg), 1, 0);
return x_4;
}
}
obj* l_coe__fn__trans___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_coe__fn__trans(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__fn__trans___rarg), 3, 0);
return x_4;
}
}
obj* l_coe__sort__trans___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_coe__sort__trans(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__sort__trans___rarg), 3, 0);
return x_4;
}
}
obj* l_coe__to__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__t___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe__to__lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__to__lift___rarg), 1, 0);
return x_4;
}
}
obj* _init_l_coe__bool__to__Prop() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_coe__sort__bool() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
uint8 l_coe__decidable__eq(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_coe__decidable__eq___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_coe__decidable__eq(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_coe__subtype___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_coe__subtype(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__subtype___rarg), 1, 0);
return x_4;
}
}
obj* l_lift__fn___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::apply_1(x_0, x_3);
x_5 = lean::apply_1(x_2, x_4);
x_6 = lean::apply_1(x_1, x_5);
return x_6;
}
}
obj* l_lift__fn(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__fn___rarg), 4, 0);
return x_8;
}
}
obj* l_lift__fn__range___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_1(x_0, x_3);
return x_4;
}
}
obj* l_lift__fn__range(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__fn__range___rarg), 3, 0);
return x_6;
}
}
obj* l_lift__fn__dom___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_lift__fn__dom(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__fn__dom___rarg), 3, 0);
return x_6;
}
}
obj* l_lift__pair___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
x_8 = lean::apply_1(x_0, x_3);
x_9 = lean::apply_1(x_1, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
 lean::cnstr_set_tag(x_7, 0);
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lift__pair(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__pair___rarg), 3, 0);
return x_8;
}
}
obj* l_lift__pair_u_2081___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_6 = x_1;
}
x_7 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
 lean::cnstr_set_tag(x_6, 0);
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
}
obj* l_lift__pair_u_2081(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__pair_u_2081___rarg), 2, 0);
return x_6;
}
}
obj* l_lift__pair_u_2082___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_6 = x_1;
}
x_7 = lean::apply_1(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
 lean::cnstr_set_tag(x_6, 0);
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lift__pair_u_2082(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__pair_u_2082___rarg), 2, 0);
return x_6;
}
}
obj* l_list_map___main___at_lift__list___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = l_list_map___main___at_lift__list___spec__1___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_list_map___main___at_lift__list___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_lift__list___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_lift__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lift__list___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lift__list(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lift__list___rarg), 2, 0);
return x_4;
}
}
void initialize_init_data_list_basic();
static bool _G_initialized = false;
void initialize_init_coe() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_list_basic();
 l_coe__bool__to__Prop = _init_l_coe__bool__to__Prop();
 l_coe__sort__bool = _init_l_coe__sort__bool();
}
