// Lean compiler output
// Module: init.control.except
// Imports: init.control.alternative init.control.lift init.data.to_string init.control.monad_fail
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
obj* l_except__t_monad__except__adapter___rarg(obj*, obj*, obj*, obj*);
obj* l_except_to__option(obj*, obj*);
obj* l_except__t_lift___rarg___closed__1;
obj* l_except__t_monad__run___rarg(obj*, obj*, obj*);
obj* l_except_monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_except__t_has__monad__lift___rarg(obj*);
obj* l_except_catch___rarg(obj*, obj*);
obj* l_monad__except_lift__except___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except_to__string(obj*, obj*);
obj* l_except_repr(obj*, obj*);
obj* l_except__t_mk(obj*, obj*, obj*);
obj* l_monad__except_orelse_x_27(obj*, obj*);
obj* l_except_has__repr(obj*, obj*);
obj* l_except_to__bool___rarg___boxed(obj*);
obj* l_except__t_monad(obj*, obj*);
obj* l_except__t_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__3(obj*, obj*);
obj* l_except__t_monad__except___rarg___lambda__1(obj*, obj*, obj*);
obj* l_except__t;
obj* l_except_repr___main(obj*, obj*);
obj* l_monad__except_orelse___rarg(obj*, obj*, obj*, obj*);
obj* l_except_map__error___main(obj*, obj*, obj*);
obj* l_except_catch(obj*, obj*);
obj* l_except_has__to__string___rarg(obj*, obj*);
obj* l_except_monad__except(obj*);
obj* l_except_monad___closed__1;
obj* l_except__t_catch___rarg___lambda__1(obj*, obj*, obj*);
obj* l_except_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_monad__except_orelse(obj*, obj*);
obj* l_function_const___rarg(obj*, obj*);
obj* l_except_map___rarg(obj*, obj*);
obj* l_except_monad___lambda__5(obj*, obj*, obj*, obj*);
obj* l_except_map__error___rarg(obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__6(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_except__t_monad__except___rarg(obj*);
obj* l_except_has__to__string(obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_except__t_monad__functor___rarg(obj*, obj*);
obj* l_except_to__option___main(obj*, obj*);
obj* l_monad__except_orelse_x_27___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*);
obj* l_except__t_bind__cont___main(obj*, obj*);
obj* l_except__t_monad__except(obj*, obj*);
obj* l_except__t_monad___rarg___lambda__5(obj*, obj*, obj*);
obj* l_except_map___main(obj*, obj*, obj*);
obj* l_monad__except_lift__except___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad__except__adapter(obj*, obj*, obj*);
obj* l_except_to__option___main___rarg(obj*);
obj* l_except__t_monad__fail(obj*);
obj* l_monad__except_orelse_x_27___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_lift___rarg(obj*, obj*, obj*);
obj* l_monad__except__adapter__trans___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_bind__cont(obj*, obj*);
obj* l_except_bind(obj*, obj*, obj*);
obj* l_monad__except_lift__except(obj*, obj*, obj*);
obj* l_except__t_return___rarg(obj*, obj*, obj*);
obj* l_except_map___main___rarg(obj*, obj*);
obj* l_except_bind___rarg(obj*, obj*);
obj* l_except_to__string___main___rarg___closed__2;
obj* l_except__t_adapt(obj*, obj*);
obj* l_except__t_monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_run(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__2(obj*, obj*);
obj* l_except_monad__except___closed__1;
obj* l_except__t_bind___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except_to__bool___main(obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__1(obj*, obj*);
obj* l_except__t_bind__cont___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except_map__error___main___rarg(obj*, obj*);
obj* l_except_repr___main___rarg(obj*, obj*, obj*);
obj* l_except_to__bool(obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_except_repr___rarg(obj*, obj*, obj*);
obj* l_except_monad(obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except_has__repr___rarg(obj*, obj*);
obj* l_except_to__string___main(obj*, obj*);
obj* l_except__t_has__monad__lift(obj*, obj*);
obj* l_except_to__string___main___rarg(obj*, obj*, obj*);
uint8 l_except_to__bool___main___rarg(obj*);
obj* l_except__t_bind__cont___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__except_orelse_x_27___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_except_monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_except_to__string___rarg(obj*, obj*, obj*);
obj* l_except__t_lift___rarg___lambda__1(obj*);
obj* l_except__t_bind(obj*, obj*);
obj* l_except_monad__except___lambda__1(obj*, obj*);
obj* l_except__t_monad__fail___rarg(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__6(obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__functor__t__trans___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_except__t_mk___rarg(obj*);
obj* l_except_return___rarg(obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__7(obj*, obj*);
obj* l_monad__except_orelse_x_27___rarg___lambda__1(obj*, uint8, obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__5(obj*, obj*);
obj* l_except__t_lift(obj*, obj*);
obj* l_except_monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_except__t_monad__run(obj*, obj*, obj*);
obj* l_monad__except_orelse_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_except_to__bool___main___rarg___boxed(obj*);
obj* l_except_return(obj*, obj*);
obj* l_except__t_run___rarg(obj*);
uint8 l_except_to__bool___rarg(obj*);
obj* l_except__t_except__t__of__except(obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__4(obj*, obj*);
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_monad__except__adapter__trans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_except_map__error(obj*, obj*, obj*);
obj* l_except__t_catch(obj*, obj*);
obj* l_except__t_except__t__of__except___rarg(obj*, obj*, obj*);
obj* l_except_to__option___rarg(obj*);
obj* l_except__t_monad___rarg___lambda__9(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except_map(obj*, obj*, obj*);
obj* l_except__t_adapt___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__except_lift__except___main(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_except__t_monad___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__except_orelse_x_27___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_except_to__string___main___rarg___closed__1;
obj* l_except__t_bind__cont___at_except__t_monad___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__8(obj*, obj*);
obj* l_except__t_catch___rarg(obj*, obj*, obj*, obj*);
obj* l_except__t_return(obj*, obj*);
obj* _init_l_except_to__string___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(error ");
return x_0;
}
}
obj* _init_l_except_to__string___main___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(ok ");
return x_0;
}
}
obj* l_except_to__string___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_except_to__string___main___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = l_option_has__repr___rarg___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::apply_1(x_1, x_15);
x_19 = l_except_to__string___main___rarg___closed__2;
lean::inc(x_19);
x_21 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_23 = l_option_has__repr___rarg___closed__3;
x_24 = lean::string_append(x_21, x_23);
return x_24;
}
}
}
obj* l_except_to__string___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__string___main___rarg), 3, 0);
return x_4;
}
}
obj* l_except_to__string___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_except_to__string___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_except_to__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__string___rarg), 3, 0);
return x_4;
}
}
obj* l_except_repr___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_except_to__string___main___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = l_option_has__repr___rarg___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::apply_1(x_1, x_15);
x_19 = l_except_to__string___main___rarg___closed__2;
lean::inc(x_19);
x_21 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_23 = l_option_has__repr___rarg___closed__3;
x_24 = lean::string_append(x_21, x_23);
return x_24;
}
}
}
obj* l_except_repr___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_repr___main___rarg), 3, 0);
return x_4;
}
}
obj* l_except_repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_except_repr___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_except_repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_repr___rarg), 3, 0);
return x_4;
}
}
obj* l_except_has__to__string___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__string___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_except_has__to__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_has__to__string___rarg), 2, 0);
return x_4;
}
}
obj* l_except_has__repr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except_repr___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_except_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_has__repr___rarg), 2, 0);
return x_4;
}
}
obj* l_except_return___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_except_return(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_return___rarg), 1, 0);
return x_4;
}
}
obj* l_except_map___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_0);
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_9 = x_1;
}
x_10 = lean::apply_1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_except_map___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except_map___main___rarg), 2, 0);
return x_6;
}
}
obj* l_except_map___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_0);
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_9 = x_1;
}
x_10 = lean::apply_1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_except_map(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except_map___rarg), 2, 0);
return x_6;
}
}
obj* l_except_map__error___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_except_map__error___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except_map__error___main___rarg), 2, 0);
return x_6;
}
}
obj* l_except_map__error___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_except_map__error(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except_map__error___rarg), 2, 0);
return x_6;
}
}
obj* l_except_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::apply_1(x_1, x_7);
return x_10;
}
}
}
obj* l_except_bind(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except_bind___rarg), 2, 0);
return x_6;
}
}
uint8 l_except_to__bool___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 1;
return x_4;
}
}
}
obj* l_except_to__bool___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__bool___main___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_except_to__bool___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_except_to__bool___main___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_except_to__bool___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 1;
return x_4;
}
}
}
obj* l_except_to__bool(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__bool___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_except_to__bool___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_except_to__bool___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_except_to__option___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
}
}
obj* l_except_to__option___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__option___main___rarg), 1, 0);
return x_4;
}
}
obj* l_except_to__option___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
}
}
obj* l_except_to__option(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_to__option___rarg), 1, 0);
return x_4;
}
}
obj* l_except_catch___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_1, x_2);
return x_5;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_except_catch(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_catch___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_except_monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_except_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except_monad___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_except_return), 2, 1);
lean::closure_set(x_3, 0, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except_monad___lambda__3), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except_monad___lambda__4), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except_monad___lambda__5), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except_bind), 3, 1);
lean::closure_set(x_8, 0, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_except_monad(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_except_monad___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* l_except_monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_13 = x_3;
}
x_14 = lean::apply_1(x_2, x_11);
if (lean::is_scalar(x_13)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_13;
}
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
obj* l_except_monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_11 = x_3;
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_2);
return x_12;
}
}
}
obj* l_except_monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_18; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_13;
 lean::cnstr_set_tag(x_13, 0);
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_22 = lean::apply_1(x_11, x_19);
if (lean::is_scalar(x_13)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_13;
}
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
}
}
obj* l_except_monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_18; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_13;
 lean::cnstr_set_tag(x_13, 0);
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_11);
return x_20;
}
}
}
}
obj* l_except_monad___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* _init_l_except__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_except__t_mk___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_except__t_mk(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_mk___rarg), 1, 0);
return x_6;
}
}
obj* l_except__t_run___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_except__t_run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_run___rarg), 1, 0);
return x_6;
}
}
obj* l_except__t_return___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_except__t_return(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_return___rarg), 3, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___main___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___rarg), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_4);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_except__t_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind___rarg), 5, 0);
return x_4;
}
}
obj* _init_l_except__t_lift___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_except__t_lift___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_13; obj* x_15; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_except__t_lift___rarg___closed__1;
lean::inc(x_13);
x_15 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_2);
return x_15;
}
}
obj* l_except__t_lift___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_except__t_lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg), 3, 0);
return x_4;
}
}
obj* l_except__t_except__t__of__except___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::apply_2(x_7, lean::box(0), x_2);
return x_10;
}
}
obj* l_except__t_except__t__of__except(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_except__t__of__except___rarg), 3, 0);
return x_4;
}
}
obj* l_except__t_has__monad__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_except__t_has__monad__lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_has__monad__lift___rarg), 1, 0);
return x_4;
}
}
obj* l_except__t_catch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_catch___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_0);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_7);
return x_8;
}
}
obj* l_except__t_catch___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
return x_7;
}
else
{
obj* x_9; obj* x_12; obj* x_15; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::apply_2(x_12, lean::box(0), x_2);
return x_15;
}
}
}
obj* l_except__t_catch(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_catch___rarg), 4, 0);
return x_4;
}
}
obj* l_except__t_monad__functor___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_except__t_monad__functor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__functor___rarg), 2, 0);
return x_12;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__2___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__3___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__4___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__5___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__6___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* l_except__t_bind__cont___at_except__t_monad___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__7___rarg), 5, 0);
return x_4;
}
}
obj* l_except__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__2), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_return___rarg), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__4), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__7), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__9), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind___rarg), 5, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_except__t_monad___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_return___rarg), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__1___rarg), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_9);
x_13 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_4, x_12);
return x_13;
}
}
obj* l_except__t_monad___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg), 2, 1);
lean::closure_set(x_7, 0, x_3);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_return___rarg), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_7);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__2___rarg), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, lean::box(0));
lean::closure_set(x_13, 2, lean::box(0));
lean::closure_set(x_13, 3, x_10);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_4, x_13);
return x_14;
}
}
obj* l_except__t_monad___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_return___rarg), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__3___rarg), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* l_except__t_monad___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__4___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* l_except__t_monad___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_1);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_except__t_monad___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__5), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__5___rarg), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_7);
return x_8;
}
}
obj* l_except__t_monad___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__6), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__6___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* l_except__t_monad___rarg___lambda__8(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_except__t_monad___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8), 2, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_except__t_monad___spec__7___rarg), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_7);
x_11 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_3, x_10);
return x_11;
}
}
obj* l_except__t_monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg), 1, 0);
return x_4;
}
}
obj* l_except__t_adapt___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_except_map__error___rarg), 2, 1);
lean::closure_set(x_16, 0, x_3);
x_17 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_16, x_4);
return x_17;
}
}
obj* l_except__t_adapt(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_adapt___rarg), 5, 0);
return x_4;
}
}
obj* l_monad__except_orelse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8), 2, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = lean::apply_3(x_5, lean::box(0), x_2, x_8);
return x_9;
}
}
obj* l_monad__except_orelse(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except_orelse___rarg), 4, 0);
return x_4;
}
}
obj* l_monad__except_orelse_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::box(x_4);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except_orelse_x_27___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_6);
lean::closure_set(x_10, 3, x_3);
x_11 = lean::apply_3(x_6, lean::box(0), x_2, x_10);
return x_11;
}
}
obj* l_monad__except_orelse_x_27___rarg___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
if (x_1 == 0)
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::apply_2(x_4, lean::box(0), x_3);
return x_8;
}
else
{
obj* x_10; 
lean::dec(x_3);
x_10 = lean::apply_2(x_4, lean::box(0), x_2);
return x_10;
}
}
}
obj* l_monad__except_orelse_x_27___rarg___lambda__2(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except_orelse_x_27___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::apply_3(x_2, lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_monad__except_orelse_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except_orelse_x_27___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_monad__except_orelse_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_monad__except_orelse_x_27___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_monad__except_orelse_x_27___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_monad__except_orelse_x_27___rarg___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_monad__except_orelse_x_27___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_monad__except_orelse_x_27___rarg___lambda__2(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_monad__except_lift__except___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_1(x_1, x_7);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_17; obj* x_20; obj* x_23; obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::apply_2(x_23, lean::box(0), x_17);
return x_26;
}
}
}
obj* l_monad__except_lift__except___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except_lift__except___main___rarg), 5, 0);
return x_6;
}
}
obj* l_monad__except_lift__except___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_1(x_1, x_7);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_17; obj* x_20; obj* x_23; obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::apply_2(x_23, lean::box(0), x_17);
return x_26;
}
}
}
obj* l_monad__except_lift__except(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except_lift__except___rarg), 5, 0);
return x_6;
}
}
obj* l_except__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__except___rarg___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_catch___rarg), 4, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_except__t_monad__except___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_except__t_monad__except(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__except___rarg), 1, 0);
return x_4;
}
}
obj* _init_l_except_monad__except___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_except_catch), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except_monad__except___lambda__1), 2, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_except_monad__except(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_except_monad__except___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* l_except_monad__except___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
}
obj* l_monad__except__adapter__trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__functor__t__trans___rarg___lambda__1), 4, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_3);
x_7 = lean::apply_3(x_0, lean::box(0), x_6, x_4);
return x_7;
}
}
obj* l_monad__except__adapter__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__except__adapter__trans___rarg), 5, 0);
return x_12;
}
}
obj* l_except__t_monad__except__adapter___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_except_map__error___rarg), 2, 1);
lean::closure_set(x_14, 0, x_2);
x_15 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_14, x_3);
return x_15;
}
}
obj* l_except__t_monad__except__adapter(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__except__adapter___rarg), 4, 0);
return x_6;
}
}
obj* l_except__t_monad__run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_2(x_0, lean::box(0), x_2);
return x_4;
}
}
obj* l_except__t_monad__run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__run___rarg), 3, 0);
return x_6;
}
}
obj* l_except__t_monad__fail___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_except__t_monad__fail(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__fail___rarg), 3, 0);
return x_2;
}
}
void initialize_init_control_alternative();
void initialize_init_control_lift();
void initialize_init_data_to__string();
void initialize_init_control_monad__fail();
static bool _G_initialized = false;
void initialize_init_control_except() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_alternative();
 initialize_init_control_lift();
 initialize_init_data_to__string();
 initialize_init_control_monad__fail();
 l_except_to__string___main___rarg___closed__1 = _init_l_except_to__string___main___rarg___closed__1();
 l_except_to__string___main___rarg___closed__2 = _init_l_except_to__string___main___rarg___closed__2();
 l_except_monad___closed__1 = _init_l_except_monad___closed__1();
 l_except__t = _init_l_except__t();
 l_except__t_lift___rarg___closed__1 = _init_l_except__t_lift___rarg___closed__1();
 l_except_monad__except___closed__1 = _init_l_except_monad__except___closed__1();
}
