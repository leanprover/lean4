// Lean compiler output
// Module: init.lean.trace
// Imports: init.lean.format init.data.rbmap.default init.lean.position init.lean.name init.lean.options
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_rbmap_insert___main___at_lean_trace_lean_trace_monad__tracer___spec__1(obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace___rarg(obj*, obj*, obj*, obj*);
unsigned char l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_monad(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_trace_pp(obj*);
obj* l_list_foldl___main___at_lean_format_join___spec__1(obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_trace_trace__t_run___rarg___lambda__1(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__12(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace__t_run(obj*, obj*);
obj* l_lean_trace_trace(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__6(obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace__t;
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace__map;
obj* l_lean_trace_lean_trace_monad__tracer(obj*);
extern obj* l_lean_format_join___closed__1;
obj* l_rbnode_insert___at_lean_trace_lean_trace_monad__tracer___spec__2(obj*, obj*, obj*);
obj* l_thunk_get___rarg(obj*);
obj* l_lean_position_decidable__lt___main(obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_lean_trace_trace__t_run___rarg(obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__7(obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_trace_trace___rarg___lambda__1(obj*, unsigned char);
obj* l_lean_kvmap_get__bool(obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___main___rarg(obj*, obj*);
obj* l_lean_trace_pp___main(obj*);
obj* l_lean_has__coe(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace___rarg___lambda__1___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_trace_pp___main___spec__1(obj*);
obj* l_rbnode_mk__insert__result___main___rarg(unsigned char, obj*);
obj* l_lean_trace_monad___rarg(obj*);
obj* l_lean_has__coe(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_lean_trace_pp___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; unsigned char x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_list_map___main___at_lean_trace_pp___main___spec__1(x_3);
x_7 = l_lean_format_join___closed__1;
lean::inc(x_7);
x_9 = l_list_foldl___main___at_lean_format_join___spec__1(x_7, x_6);
x_10 = lean::mk_nat_obj(2u);
x_11 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_12);
x_14 = x_13;
return x_14;
}
}
obj* l_list_map___main___at_lean_trace_pp___main___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; unsigned char x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_lean_trace_pp___main(x_3);
x_9 = 0;
x_10 = lean::alloc_cnstr(1, 0, 0);
;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_list_map___main___at_lean_trace_pp___main___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_lean_trace_pp(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_trace_pp___main(x_0);
return x_1;
}
}
obj* _init_l_lean_trace_trace__map() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_trace_trace__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_trace_monad___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_state__t_monad___rarg(x_0);
return x_1;
}
}
obj* l_lean_trace_monad(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_monad___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_trace_trace___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_trace___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_7, 0, x_0);
x_8 = lean::apply_4(x_4, lean::box(0), x_2, x_3, x_7);
return x_8;
}
}
obj* l_lean_trace_trace___rarg___lambda__1(obj* x_0, unsigned char x_1) {
_start:
{
obj* x_2; obj* x_5; unsigned char x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::apply_2(x_5, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_trace_trace(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_trace___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_trace_trace___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_lean_trace_trace___rarg___lambda__1(x_0, x_2);
return x_3;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__5), 7, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__12), 6, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_5 = x_2;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::apply_2(x_1, lean::box(0), x_6);
return x_7;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_22; unsigned char x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 3);
lean::inc(x_14);
lean::inc(x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_14);
x_18 = l_rbnode_insert___at_lean_trace_lean_trace_monad__tracer___spec__2(x_12, x_1, x_17);
x_19 = lean::cnstr_get(x_7, 2);
lean::inc(x_19);
lean::dec(x_7);
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_19);
lean::cnstr_set(x_22, 3, x_14);
x_23 = 0;
x_24 = lean::box(x_23);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_9;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::inc(x_2);
x_27 = lean::apply_2(x_2, lean::box(0), x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1), 3, 2);
lean::closure_set(x_28, 0, x_5);
lean::closure_set(x_28, 1, x_2);
x_29 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_27, x_28);
return x_29;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = l_thunk_get___rarg(x_0);
x_10 = lean::apply_1(x_9, x_6);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__2), 5, 4);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_2);
lean::closure_set(x_12, 2, x_3);
lean::closure_set(x_12, 3, x_4);
x_13 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; unsigned char x_12; obj* x_14; obj* x_17; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
x_17 = l_lean_kvmap_get__bool(x_14, x_5);
if (lean::obj_tag(x_17) == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_17);
x_24 = l_thunk_get___rarg(x_2);
x_25 = lean::apply_1(x_24, x_9);
return x_25;
}
else
{
obj* x_26; unsigned char x_29; 
x_26 = lean::cnstr_get(x_17, 0);
lean::inc(x_26);
lean::dec(x_17);
x_29 = lean::unbox(x_26);
lean::dec(x_26);
if (x_29 == 0)
{
obj* x_36; obj* x_37; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_36 = l_thunk_get___rarg(x_2);
x_37 = lean::apply_1(x_36, x_9);
return x_37;
}
else
{
unsigned char x_38; 
x_38 = 0;
x_12 = x_38;
goto lbl_13;
}
}
lbl_13:
{
obj* x_39; obj* x_41; obj* x_45; obj* x_46; obj* x_47; unsigned char x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; 
x_39 = lean::cnstr_get(x_9, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_9, 1);
lean::inc(x_41);
lean::dec(x_9);
lean::inc(x_0);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_0);
x_46 = lean::alloc_cnstr(0, 0, 0);
;
x_47 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_47, 0, x_39);
lean::cnstr_set(x_47, 1, x_41);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_46);
x_48 = 0;
x_49 = lean::box(x_48);
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
lean::inc(x_1);
x_52 = lean::apply_2(x_1, lean::box(0), x_50);
lean::inc(x_4);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__3), 6, 5);
lean::closure_set(x_54, 0, x_2);
lean::closure_set(x_54, 1, x_3);
lean::closure_set(x_54, 2, x_0);
lean::closure_set(x_54, 3, x_1);
lean::closure_set(x_54, 4, x_4);
x_55 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_52, x_54);
return x_55;
}
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_17; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
lean::inc(x_6);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_6);
lean::inc(x_13);
x_19 = lean::apply_2(x_13, lean::box(0), x_17);
lean::inc(x_8);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__4), 7, 6);
lean::closure_set(x_21, 0, x_2);
lean::closure_set(x_21, 1, x_13);
lean::closure_set(x_21, 2, x_5);
lean::closure_set(x_21, 3, x_4);
lean::closure_set(x_21, 4, x_8);
lean::closure_set(x_21, 5, x_3);
x_22 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_19, x_21);
return x_22;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 0, 0);
;
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 2, x_6);
lean::cnstr_set(x_10, 3, x_7);
return x_10;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set(x_9, 2, x_0);
lean::cnstr_set(x_9, 3, x_6);
return x_9;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; unsigned char x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 3);
lean::inc(x_17);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_8, 3);
lean::inc(x_20);
lean::dec(x_8);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_2);
x_25 = l_list_append___main___rarg(x_17, x_24);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_13);
lean::cnstr_set(x_26, 2, x_15);
lean::cnstr_set(x_26, 3, x_25);
x_27 = 0;
x_28 = lean::box(x_27);
if (lean::is_scalar(x_10)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_10;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
lean::inc(x_3);
x_31 = lean::apply_2(x_3, lean::box(0), x_29);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1), 3, 2);
lean::closure_set(x_32, 0, x_6);
lean::closure_set(x_32, 1, x_3);
x_33 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_31, x_32);
return x_33;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = l_thunk_get___rarg(x_0);
x_11 = lean::apply_1(x_10, x_7);
lean::inc(x_5);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__8), 6, 5);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_4);
lean::closure_set(x_13, 4, x_5);
x_14 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_9);
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_23 = l_thunk_get___rarg(x_0);
x_24 = lean::apply_1(x_23, x_11);
return x_24;
}
else
{
obj* x_26; unsigned char x_28; unsigned char x_30; obj* x_33; 
lean::dec(x_9);
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
lean::inc(x_26);
x_33 = l_lean_kvmap_get__bool(x_26, x_7);
if (lean::obj_tag(x_33) == 0)
{
unsigned char x_39; 
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_33);
x_39 = 0;
x_28 = x_39;
goto lbl_29;
}
else
{
obj* x_40; unsigned char x_43; 
x_40 = lean::cnstr_get(x_33, 0);
lean::inc(x_40);
lean::dec(x_33);
x_43 = lean::unbox(x_40);
lean::dec(x_40);
if (x_43 == 0)
{
unsigned char x_49; 
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
x_49 = 0;
x_28 = x_49;
goto lbl_29;
}
else
{
unsigned char x_52; 
lean::dec(x_11);
lean::dec(x_3);
x_52 = 0;
x_30 = x_52;
goto lbl_31;
}
}
lbl_29:
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__6), 3, 2);
lean::closure_set(x_53, 0, x_1);
lean::closure_set(x_53, 1, x_26);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__7), 2, 1);
lean::closure_set(x_54, 0, x_2);
x_55 = l_thunk_get___rarg(x_0);
x_56 = l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg(x_3, lean::box(0), x_53, x_54, x_55, x_11);
return x_56;
}
lbl_31:
{
obj* x_57; obj* x_59; obj* x_61; unsigned char x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_69; 
x_57 = lean::cnstr_get(x_1, 1);
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 0, 0);
;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_26);
lean::cnstr_set(x_61, 1, x_57);
lean::cnstr_set(x_61, 2, x_2);
lean::cnstr_set(x_61, 3, x_59);
x_62 = 0;
x_63 = lean::box(x_62);
if (lean::is_scalar(x_13)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_13;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_61);
lean::inc(x_4);
x_66 = lean::apply_2(x_4, lean::box(0), x_64);
lean::inc(x_6);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__9), 7, 6);
lean::closure_set(x_68, 0, x_0);
lean::closure_set(x_68, 1, x_1);
lean::closure_set(x_68, 2, x_5);
lean::closure_set(x_68, 3, x_59);
lean::closure_set(x_68, 4, x_4);
lean::closure_set(x_68, 5, x_6);
x_69 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_66, x_68);
return x_69;
}
}
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = lean::cnstr_get(x_7, 2);
lean::inc(x_12);
lean::inc(x_12);
if (lean::is_scalar(x_11)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_11;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_9);
lean::inc(x_0);
x_17 = lean::apply_2(x_0, lean::box(0), x_15);
lean::inc(x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__10), 9, 8);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_7);
lean::closure_set(x_19, 2, x_12);
lean::closure_set(x_19, 3, x_2);
lean::closure_set(x_19, 4, x_0);
lean::closure_set(x_19, 5, x_3);
lean::closure_set(x_19, 6, x_4);
lean::closure_set(x_19, 7, x_5);
x_20 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_17, x_19);
return x_20;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
lean::inc(x_5);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_5);
lean::inc(x_11);
x_17 = lean::apply_2(x_11, lean::box(0), x_15);
lean::inc(x_7);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__11), 7, 6);
lean::closure_set(x_19, 0, x_11);
lean::closure_set(x_19, 1, x_4);
lean::closure_set(x_19, 2, x_0);
lean::closure_set(x_19, 3, x_3);
lean::closure_set(x_19, 4, x_7);
lean::closure_set(x_19, 5, x_2);
x_20 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_17, x_19);
return x_20;
}
}
obj* l_lean_trace_lean_trace_monad__tracer(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_position_decidable__lt___main(x_1, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_16);
lean::inc(x_1);
lean::inc(x_7);
x_20 = l_lean_position_decidable__lt___main(x_7, x_1);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; 
lean::dec(x_20);
lean::dec(x_7);
lean::dec(x_9);
if (lean::is_scalar(x_13)) {
 x_24 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_24 = x_13;
}
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_1);
lean::cnstr_set(x_24, 2, x_2);
lean::cnstr_set(x_24, 3, x_11);
return x_24;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_20);
x_26 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_7);
lean::cnstr_set(x_27, 2, x_9);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_16);
x_29 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_position_decidable__lt___main(x_1, x_33);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; 
lean::dec(x_42);
lean::inc(x_1);
lean::inc(x_33);
x_46 = l_lean_position_decidable__lt___main(x_33, x_1);
if (lean::obj_tag(x_46) == 0)
{
obj* x_50; 
lean::dec(x_46);
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_50 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_50 = x_39;
}
lean::cnstr_set(x_50, 0, x_31);
lean::cnstr_set(x_50, 1, x_1);
lean::cnstr_set(x_50, 2, x_2);
lean::cnstr_set(x_50, 3, x_37);
return x_50;
}
else
{
unsigned char x_53; 
lean::dec(x_46);
lean::inc(x_37);
x_53 = l_rbnode_get__color___main___rarg(x_37);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_39);
x_55 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_37, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_33, x_35, x_31);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_39;
}
lean::cnstr_set(x_58, 0, x_31);
lean::cnstr_set(x_58, 1, x_33);
lean::cnstr_set(x_58, 2, x_35);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
unsigned char x_61; 
lean::dec(x_42);
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_trace_lean_trace_monad__tracer___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_trace_lean_trace_monad__tracer___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_trace_lean_trace_monad__tracer___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_7 = lean::apply_1(x_2, x_5);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_4, x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_3);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; 
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
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::apply_1(x_1, x_5);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_3);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::apply_2(x_11, lean::box(0), x_15);
return x_16;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg), 6, 0);
return x_2;
}
}
obj* l_lean_trace_trace__t_run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 0, 0);
;
lean::inc(x_5);
lean::inc(x_5);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_5);
x_9 = lean::apply_1(x_2, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_trace__t_run___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_0);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_lean_trace_trace__t_run___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
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
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_4, 1);
lean::inc(x_13);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_6;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_13);
x_17 = lean::apply_2(x_10, lean::box(0), x_16);
return x_17;
}
}
obj* l_lean_trace_trace__t_run(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_trace__t_run___rarg), 3, 0);
return x_4;
}
}
void initialize_init_lean_format();
void initialize_init_data_rbmap_default();
void initialize_init_lean_position();
void initialize_init_lean_name();
void initialize_init_lean_options();
static bool _G_initialized = false;
void initialize_init_lean_trace() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_format();
 initialize_init_data_rbmap_default();
 initialize_init_lean_position();
 initialize_init_lean_name();
 initialize_init_lean_options();
 l_lean_trace_trace__map = _init_l_lean_trace_trace__map();
 l_lean_trace_trace__t = _init_l_lean_trace_trace__t();
}
