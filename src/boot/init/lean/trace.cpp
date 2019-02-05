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
obj* l_lean_trace_trace___rarg___lambda__1(obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__7(obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_trace_pp___main(obj*);
obj* l_lean_trace_trace__map;
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_format_join___closed__1;
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace__t_run(obj*, obj*);
obj* l_lean_kvmap_get__bool(obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer(obj*);
obj* l_rbnode_ins___main___at_lean_trace_lean_trace_monad__tracer___spec__3(obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(unsigned char, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__12(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___main___rarg(obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace__t_run___rarg___lambda__1(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_trace_lean_trace_monad__tracer___spec__1(obj*, obj*, obj*);
obj* l_lean_trace_monad(obj*);
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_trace_trace___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_has__coe(obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace(obj*);
obj* l_list_foldl___main___at_lean_format_join___spec__1(obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_trace_trace__t_run___rarg(obj*, obj*, obj*);
unsigned char l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_trace_monad___rarg(obj*);
obj* l_lean_trace_trace__t;
obj* l_lean_position_decidable__lt___main(obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4(obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_trace_pp(obj*);
obj* l_rbnode_insert___at_lean_trace_lean_trace_monad__tracer___spec__2(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_trace_pp___main___spec__1(obj*);
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__6(obj*, obj*, obj*);
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
x_2 = lean::box(0);
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
x_10 = lean::box(1);
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
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_trace___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_0);
x_8 = lean::mk_thunk(x_7);
x_9 = lean::apply_4(x_4, lean::box(0), x_2, x_3, x_8);
return x_9;
}
}
obj* l_lean_trace_trace___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
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
x_23 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_9;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
lean::inc(x_2);
x_26 = lean::apply_2(x_2, lean::box(0), x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1), 3, 2);
lean::closure_set(x_27, 0, x_5);
lean::closure_set(x_27, 1, x_2);
x_28 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_26, x_27);
return x_28;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::thunk_get(x_0);
lean::dec(x_0);
x_11 = lean::apply_1(x_9, x_6);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__2), 5, 4);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_4);
x_14 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_17; 
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
obj* x_24; obj* x_26; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_24 = lean::thunk_get(x_2);
lean::dec(x_2);
x_26 = lean::apply_1(x_24, x_9);
return x_26;
}
else
{
obj* x_27; unsigned char x_30; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
lean::dec(x_17);
x_30 = lean::unbox(x_27);
lean::dec(x_27);
if (x_30 == 0)
{
obj* x_37; obj* x_39; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_37 = lean::thunk_get(x_2);
lean::dec(x_2);
x_39 = lean::apply_1(x_37, x_9);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::box(0);
x_12 = x_40;
goto lbl_13;
}
}
lbl_13:
{
obj* x_42; obj* x_44; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_12);
x_42 = lean::cnstr_get(x_9, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_9, 1);
lean::inc(x_44);
lean::dec(x_9);
lean::inc(x_0);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_0);
x_49 = lean::box(0);
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_42);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_48);
lean::cnstr_set(x_51, 3, x_49);
if (lean::is_scalar(x_11)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_11;
}
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_51);
lean::inc(x_1);
x_54 = lean::apply_2(x_1, lean::box(0), x_52);
lean::inc(x_4);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__3), 6, 5);
lean::closure_set(x_56, 0, x_2);
lean::closure_set(x_56, 1, x_3);
lean::closure_set(x_56, 2, x_0);
lean::closure_set(x_56, 3, x_1);
lean::closure_set(x_56, 4, x_4);
x_57 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_54, x_56);
return x_57;
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
x_6 = lean::box(0);
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
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
x_27 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
lean::inc(x_3);
x_30 = lean::apply_2(x_3, lean::box(0), x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__1), 3, 2);
lean::closure_set(x_31, 0, x_6);
lean::closure_set(x_31, 1, x_3);
x_32 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_30, x_31);
return x_32;
}
}
obj* l_lean_trace_lean_trace_monad__tracer___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::thunk_get(x_0);
lean::dec(x_0);
x_12 = lean::apply_1(x_10, x_7);
lean::inc(x_5);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__8), 6, 5);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_3);
lean::closure_set(x_14, 3, x_4);
lean::closure_set(x_14, 4, x_5);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_12, x_14);
return x_15;
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
obj* x_23; obj* x_25; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_23 = lean::thunk_get(x_0);
lean::dec(x_0);
x_25 = lean::apply_1(x_23, x_11);
return x_25;
}
else
{
obj* x_27; obj* x_29; obj* x_31; obj* x_34; 
lean::dec(x_9);
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
lean::inc(x_27);
x_34 = l_lean_kvmap_get__bool(x_27, x_7);
if (lean::obj_tag(x_34) == 0)
{
obj* x_40; 
lean::dec(x_5);
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_34);
x_40 = lean::box(0);
x_29 = x_40;
goto lbl_30;
}
else
{
obj* x_41; unsigned char x_44; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
lean::dec(x_34);
x_44 = lean::unbox(x_41);
lean::dec(x_41);
if (x_44 == 0)
{
obj* x_50; 
lean::dec(x_5);
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_6);
x_50 = lean::box(0);
x_29 = x_50;
goto lbl_30;
}
else
{
obj* x_53; 
lean::dec(x_11);
lean::dec(x_3);
x_53 = lean::box(0);
x_31 = x_53;
goto lbl_32;
}
}
lbl_30:
{
obj* x_55; obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_29);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__6), 3, 2);
lean::closure_set(x_55, 0, x_1);
lean::closure_set(x_55, 1, x_27);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__7), 2, 1);
lean::closure_set(x_56, 0, x_2);
x_57 = lean::thunk_get(x_0);
lean::dec(x_0);
x_59 = l_monad__state__adapter_adapt__state_x_27___at_lean_trace_lean_trace_monad__tracer___spec__4___rarg(x_3, lean::box(0), x_55, x_56, x_57, x_11);
return x_59;
}
lbl_32:
{
obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_31);
x_61 = lean::cnstr_get(x_1, 1);
lean::inc(x_61);
x_63 = lean::box(0);
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_65, 0, x_27);
lean::cnstr_set(x_65, 1, x_61);
lean::cnstr_set(x_65, 2, x_2);
lean::cnstr_set(x_65, 3, x_63);
lean::inc(x_63);
if (lean::is_scalar(x_13)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_13;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set(x_67, 1, x_65);
lean::inc(x_4);
x_69 = lean::apply_2(x_4, lean::box(0), x_67);
lean::inc(x_6);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_trace_lean_trace_monad__tracer___rarg___lambda__9), 7, 6);
lean::closure_set(x_71, 0, x_0);
lean::closure_set(x_71, 1, x_1);
lean::closure_set(x_71, 2, x_5);
lean::closure_set(x_71, 3, x_63);
lean::closure_set(x_71, 4, x_4);
lean::closure_set(x_71, 5, x_6);
x_72 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_69, x_71);
return x_72;
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
lean::dec(x_9);
lean::dec(x_7);
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
x_5 = lean::box(0);
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
