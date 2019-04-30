// Lean compiler output
// Module: init.lean.trace
// Imports: init.lean.format init.data.rbmap.default init.lean.position init.lean.name init.lean.options
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
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_Trace_Monad(obj*);
obj* l_List_map___main___at_Lean_Trace_pp___main___spec__1(obj*);
obj* l_Lean_Trace_Trace___rarg___lambda__1___boxed(obj*, obj*);
obj* l_StateT_Monad___rarg(obj*);
obj* l_Lean_Trace_pp___main(obj*);
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2(obj*);
obj* l_Lean_HasCoe(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Trace___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__12___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_TraceT_run___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Trace_pp(obj*);
obj* l_Lean_Trace_Monad___boxed(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__6___boxed(obj*, obj*, obj*);
uint8 l_Lean_KVMap_getBool(obj*, obj*, uint8);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___boxed(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___boxed(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_TraceT_run(obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__6(obj*, obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_HasCoe___boxed(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Trace_Trace___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__12(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Trace___boxed(obj*);
obj* l_Lean_Trace_Trace(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__9___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Position_lt___main(obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Monad___rarg(obj*);
obj* l_Lean_Trace_TraceT_run___rarg(obj*, obj*, obj*);
obj* l_Lean_Trace_TraceT_run___boxed(obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(obj*, obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Format_join(obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__7(obj*, obj*);
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_HasCoe(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_HasCoe___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_HasCoe(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Trace_pp___main___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_Lean_Trace_pp___main(x_2);
x_8 = 0;
x_9 = lean::box(1);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = x_10;
x_12 = l_List_map___main___at_Lean_Trace_pp___main___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_Lean_Trace_pp___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_List_map___main___at_Lean_Trace_pp___main___spec__1(x_3);
x_7 = l_Lean_Format_join(x_6);
x_8 = lean::mk_nat_obj(2ul);
x_9 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = 0;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = x_11;
return x_12;
}
}
obj* l_Lean_Trace_pp(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Trace_pp___main(x_0);
return x_1;
}
}
obj* l_Lean_Trace_Monad___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_StateT_Monad___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Trace_Monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Monad___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Trace_Monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Trace_Monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Trace_Trace___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* l_Lean_Trace_Trace___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Trace___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_7, 0, x_0);
x_8 = lean::mk_thunk(x_7);
x_9 = lean::apply_4(x_4, lean::box(0), x_2, x_3, x_8);
return x_9;
}
}
obj* l_Lean_Trace_Trace(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Trace___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_Trace_Trace___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Trace_Trace___rarg___lambda__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Trace_Trace___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Trace_Trace(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_18; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
lean::inc(x_9);
lean::inc(x_1);
x_18 = l_Lean_Position_lt___main(x_1, x_9);
if (x_18 == 0)
{
uint8 x_21; 
lean::inc(x_1);
lean::inc(x_9);
x_21 = l_Lean_Position_lt___main(x_9, x_1);
if (x_21 == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_15;
}
lean::cnstr_set(x_24, 0, x_7);
lean::cnstr_set(x_24, 1, x_1);
lean::cnstr_set(x_24, 2, x_2);
lean::cnstr_set(x_24, 3, x_13);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
x_25 = x_24;
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_15;
}
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_9);
lean::cnstr_set(x_27, 2, x_11);
lean::cnstr_set(x_27, 3, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_6);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_30 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_30 = x_15;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_9);
lean::cnstr_set(x_30, 2, x_11);
lean::cnstr_set(x_30, 3, x_13);
lean::cnstr_set_scalar(x_30, sizeof(void*)*4, x_6);
x_31 = x_30;
return x_31;
}
}
else
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; uint8 x_43; 
x_32 = lean::cnstr_get(x_0, 0);
x_34 = lean::cnstr_get(x_0, 1);
x_36 = lean::cnstr_get(x_0, 2);
x_38 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_40 = x_0;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_0);
 x_40 = lean::box(0);
}
lean::inc(x_34);
lean::inc(x_1);
x_43 = l_Lean_Position_lt___main(x_1, x_34);
if (x_43 == 0)
{
uint8 x_46; 
lean::inc(x_1);
lean::inc(x_34);
x_46 = l_Lean_Position_lt___main(x_34, x_1);
if (x_46 == 0)
{
obj* x_49; obj* x_50; 
lean::dec(x_34);
lean::dec(x_36);
if (lean::is_scalar(x_40)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_40;
}
lean::cnstr_set(x_49, 0, x_32);
lean::cnstr_set(x_49, 1, x_1);
lean::cnstr_set(x_49, 2, x_2);
lean::cnstr_set(x_49, 3, x_38);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
uint8 x_51; 
x_51 = l_RBNode_isRed___main___rarg(x_38);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; 
x_52 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_38, x_1, x_2);
if (lean::is_scalar(x_40)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_40;
}
lean::cnstr_set(x_53, 0, x_32);
lean::cnstr_set(x_53, 1, x_34);
lean::cnstr_set(x_53, 2, x_36);
lean::cnstr_set(x_53, 3, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_6);
x_54 = x_53;
return x_54;
}
else
{
obj* x_55; 
x_55 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_38, x_1, x_2);
if (lean::obj_tag(x_55) == 0)
{
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_40);
lean::dec(x_32);
return x_55;
}
else
{
obj* x_60; 
x_60 = lean::cnstr_get(x_55, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_62; 
x_62 = lean::cnstr_get(x_55, 3);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; 
x_64 = lean::cnstr_get(x_55, 1);
x_66 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 3);
 x_68 = x_55;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_55);
 x_68 = lean::box(0);
}
x_69 = 0;
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_62);
lean::cnstr_set(x_70, 1, x_64);
lean::cnstr_set(x_70, 2, x_66);
lean::cnstr_set(x_70, 3, x_62);
lean::cnstr_set_scalar(x_70, sizeof(void*)*4, x_69);
x_71 = x_70;
x_72 = 1;
if (lean::is_scalar(x_40)) {
 x_73 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_73 = x_40;
}
lean::cnstr_set(x_73, 0, x_32);
lean::cnstr_set(x_73, 1, x_34);
lean::cnstr_set(x_73, 2, x_36);
lean::cnstr_set(x_73, 3, x_71);
lean::cnstr_set_scalar(x_73, sizeof(void*)*4, x_72);
x_74 = x_73;
return x_74;
}
else
{
uint8 x_75; 
x_75 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*4);
if (x_75 == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_76 = lean::cnstr_get(x_55, 1);
x_78 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 3);
 x_80 = x_55;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_55);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_62, 0);
x_83 = lean::cnstr_get(x_62, 1);
x_85 = lean::cnstr_get(x_62, 2);
x_87 = lean::cnstr_get(x_62, 3);
if (lean::is_exclusive(x_62)) {
 x_89 = x_62;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_62);
 x_89 = lean::box(0);
}
x_90 = 1;
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_32);
lean::cnstr_set(x_91, 1, x_34);
lean::cnstr_set(x_91, 2, x_36);
lean::cnstr_set(x_91, 3, x_60);
lean::cnstr_set_scalar(x_91, sizeof(void*)*4, x_90);
x_92 = x_91;
if (lean::is_scalar(x_80)) {
 x_93 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_93 = x_80;
}
lean::cnstr_set(x_93, 0, x_81);
lean::cnstr_set(x_93, 1, x_83);
lean::cnstr_set(x_93, 2, x_85);
lean::cnstr_set(x_93, 3, x_87);
lean::cnstr_set_scalar(x_93, sizeof(void*)*4, x_90);
x_94 = x_93;
if (lean::is_scalar(x_40)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_40;
}
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set(x_95, 1, x_76);
lean::cnstr_set(x_95, 2, x_78);
lean::cnstr_set(x_95, 3, x_94);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_75);
x_96 = x_95;
return x_96;
}
else
{
obj* x_97; obj* x_99; obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_97 = lean::cnstr_get(x_55, 1);
x_99 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 3);
 x_101 = x_55;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_55);
 x_101 = lean::box(0);
}
x_102 = 0;
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_60);
lean::cnstr_set(x_103, 1, x_97);
lean::cnstr_set(x_103, 2, x_99);
lean::cnstr_set(x_103, 3, x_62);
lean::cnstr_set_scalar(x_103, sizeof(void*)*4, x_102);
x_104 = x_103;
if (lean::is_scalar(x_40)) {
 x_105 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_105 = x_40;
}
lean::cnstr_set(x_105, 0, x_32);
lean::cnstr_set(x_105, 1, x_34);
lean::cnstr_set(x_105, 2, x_36);
lean::cnstr_set(x_105, 3, x_104);
lean::cnstr_set_scalar(x_105, sizeof(void*)*4, x_75);
x_106 = x_105;
return x_106;
}
}
}
else
{
uint8 x_107; 
x_107 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*4);
if (x_107 == 0)
{
obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; uint8 x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_108 = lean::cnstr_get(x_55, 1);
x_110 = lean::cnstr_get(x_55, 2);
x_112 = lean::cnstr_get(x_55, 3);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_114 = x_55;
} else {
 lean::inc(x_108);
 lean::inc(x_110);
 lean::inc(x_112);
 lean::dec(x_55);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_60, 0);
x_117 = lean::cnstr_get(x_60, 1);
x_119 = lean::cnstr_get(x_60, 2);
x_121 = lean::cnstr_get(x_60, 3);
if (lean::is_exclusive(x_60)) {
 x_123 = x_60;
} else {
 lean::inc(x_115);
 lean::inc(x_117);
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_60);
 x_123 = lean::box(0);
}
x_124 = 1;
if (lean::is_scalar(x_123)) {
 x_125 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_125 = x_123;
}
lean::cnstr_set(x_125, 0, x_32);
lean::cnstr_set(x_125, 1, x_34);
lean::cnstr_set(x_125, 2, x_36);
lean::cnstr_set(x_125, 3, x_115);
lean::cnstr_set_scalar(x_125, sizeof(void*)*4, x_124);
x_126 = x_125;
if (lean::is_scalar(x_114)) {
 x_127 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_127 = x_114;
}
lean::cnstr_set(x_127, 0, x_121);
lean::cnstr_set(x_127, 1, x_108);
lean::cnstr_set(x_127, 2, x_110);
lean::cnstr_set(x_127, 3, x_112);
lean::cnstr_set_scalar(x_127, sizeof(void*)*4, x_124);
x_128 = x_127;
if (lean::is_scalar(x_40)) {
 x_129 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_129 = x_40;
}
lean::cnstr_set(x_129, 0, x_126);
lean::cnstr_set(x_129, 1, x_117);
lean::cnstr_set(x_129, 2, x_119);
lean::cnstr_set(x_129, 3, x_128);
lean::cnstr_set_scalar(x_129, sizeof(void*)*4, x_107);
x_130 = x_129;
return x_130;
}
else
{
obj* x_131; 
x_131 = lean::cnstr_get(x_55, 3);
lean::inc(x_131);
if (lean::obj_tag(x_131) == 0)
{
obj* x_133; obj* x_135; obj* x_137; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_133 = lean::cnstr_get(x_55, 1);
x_135 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 3);
 x_137 = x_55;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_55);
 x_137 = lean::box(0);
}
x_138 = 0;
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_60);
lean::cnstr_set(x_139, 1, x_133);
lean::cnstr_set(x_139, 2, x_135);
lean::cnstr_set(x_139, 3, x_131);
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_138);
x_140 = x_139;
if (lean::is_scalar(x_40)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_40;
}
lean::cnstr_set(x_141, 0, x_32);
lean::cnstr_set(x_141, 1, x_34);
lean::cnstr_set(x_141, 2, x_36);
lean::cnstr_set(x_141, 3, x_140);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_107);
x_142 = x_141;
return x_142;
}
else
{
uint8 x_143; 
x_143 = lean::cnstr_get_scalar<uint8>(x_131, sizeof(void*)*4);
if (x_143 == 0)
{
obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_40);
x_145 = lean::cnstr_get(x_55, 1);
x_147 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 3);
 x_149 = x_55;
} else {
 lean::inc(x_145);
 lean::inc(x_147);
 lean::dec(x_55);
 x_149 = lean::box(0);
}
x_150 = lean::cnstr_get(x_131, 0);
x_152 = lean::cnstr_get(x_131, 1);
x_154 = lean::cnstr_get(x_131, 2);
x_156 = lean::cnstr_get(x_131, 3);
if (lean::is_exclusive(x_131)) {
 x_158 = x_131;
} else {
 lean::inc(x_150);
 lean::inc(x_152);
 lean::inc(x_154);
 lean::inc(x_156);
 lean::dec(x_131);
 x_158 = lean::box(0);
}
lean::inc(x_60);
if (lean::is_scalar(x_158)) {
 x_160 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_160 = x_158;
}
lean::cnstr_set(x_160, 0, x_32);
lean::cnstr_set(x_160, 1, x_34);
lean::cnstr_set(x_160, 2, x_36);
lean::cnstr_set(x_160, 3, x_60);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 lean::cnstr_release(x_60, 2);
 lean::cnstr_release(x_60, 3);
 x_161 = x_60;
} else {
 lean::dec(x_60);
 x_161 = lean::box(0);
}
lean::cnstr_set_scalar(x_160, sizeof(void*)*4, x_107);
x_162 = x_160;
if (lean::is_scalar(x_161)) {
 x_163 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_163 = x_161;
}
lean::cnstr_set(x_163, 0, x_150);
lean::cnstr_set(x_163, 1, x_152);
lean::cnstr_set(x_163, 2, x_154);
lean::cnstr_set(x_163, 3, x_156);
lean::cnstr_set_scalar(x_163, sizeof(void*)*4, x_107);
x_164 = x_163;
if (lean::is_scalar(x_149)) {
 x_165 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_165 = x_149;
}
lean::cnstr_set(x_165, 0, x_162);
lean::cnstr_set(x_165, 1, x_145);
lean::cnstr_set(x_165, 2, x_147);
lean::cnstr_set(x_165, 3, x_164);
lean::cnstr_set_scalar(x_165, sizeof(void*)*4, x_143);
x_166 = x_165;
return x_166;
}
else
{
obj* x_167; obj* x_169; obj* x_171; obj* x_172; obj* x_174; obj* x_176; obj* x_178; obj* x_180; obj* x_181; obj* x_182; uint8 x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_167 = lean::cnstr_get(x_55, 1);
x_169 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 3);
 x_171 = x_55;
} else {
 lean::inc(x_167);
 lean::inc(x_169);
 lean::dec(x_55);
 x_171 = lean::box(0);
}
x_172 = lean::cnstr_get(x_60, 0);
x_174 = lean::cnstr_get(x_60, 1);
x_176 = lean::cnstr_get(x_60, 2);
x_178 = lean::cnstr_get(x_60, 3);
if (lean::is_exclusive(x_60)) {
 x_180 = x_60;
} else {
 lean::inc(x_172);
 lean::inc(x_174);
 lean::inc(x_176);
 lean::inc(x_178);
 lean::dec(x_60);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_172);
lean::cnstr_set(x_181, 1, x_174);
lean::cnstr_set(x_181, 2, x_176);
lean::cnstr_set(x_181, 3, x_178);
lean::cnstr_set_scalar(x_181, sizeof(void*)*4, x_143);
x_182 = x_181;
x_183 = 0;
if (lean::is_scalar(x_171)) {
 x_184 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_184 = x_171;
}
lean::cnstr_set(x_184, 0, x_182);
lean::cnstr_set(x_184, 1, x_167);
lean::cnstr_set(x_184, 2, x_169);
lean::cnstr_set(x_184, 3, x_131);
lean::cnstr_set_scalar(x_184, sizeof(void*)*4, x_183);
x_185 = x_184;
if (lean::is_scalar(x_40)) {
 x_186 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_186 = x_40;
}
lean::cnstr_set(x_186, 0, x_32);
lean::cnstr_set(x_186, 1, x_34);
lean::cnstr_set(x_186, 2, x_36);
lean::cnstr_set(x_186, 3, x_185);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_143);
x_187 = x_186;
return x_187;
}
}
}
}
}
}
}
}
else
{
uint8 x_188; 
x_188 = l_RBNode_isRed___main___rarg(x_32);
if (x_188 == 0)
{
obj* x_189; obj* x_190; obj* x_191; 
x_189 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_32, x_1, x_2);
if (lean::is_scalar(x_40)) {
 x_190 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_190 = x_40;
}
lean::cnstr_set(x_190, 0, x_189);
lean::cnstr_set(x_190, 1, x_34);
lean::cnstr_set(x_190, 2, x_36);
lean::cnstr_set(x_190, 3, x_38);
lean::cnstr_set_scalar(x_190, sizeof(void*)*4, x_6);
x_191 = x_190;
return x_191;
}
else
{
obj* x_192; 
x_192 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_32, x_1, x_2);
if (lean::obj_tag(x_192) == 0)
{
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_40);
lean::dec(x_38);
return x_192;
}
else
{
obj* x_197; 
x_197 = lean::cnstr_get(x_192, 0);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_199; 
x_199 = lean::cnstr_get(x_192, 3);
lean::inc(x_199);
if (lean::obj_tag(x_199) == 0)
{
obj* x_201; obj* x_203; obj* x_205; uint8 x_206; obj* x_207; obj* x_208; uint8 x_209; obj* x_210; obj* x_211; 
x_201 = lean::cnstr_get(x_192, 1);
x_203 = lean::cnstr_get(x_192, 2);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 3);
 x_205 = x_192;
} else {
 lean::inc(x_201);
 lean::inc(x_203);
 lean::dec(x_192);
 x_205 = lean::box(0);
}
x_206 = 0;
if (lean::is_scalar(x_205)) {
 x_207 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_207 = x_205;
}
lean::cnstr_set(x_207, 0, x_199);
lean::cnstr_set(x_207, 1, x_201);
lean::cnstr_set(x_207, 2, x_203);
lean::cnstr_set(x_207, 3, x_199);
lean::cnstr_set_scalar(x_207, sizeof(void*)*4, x_206);
x_208 = x_207;
x_209 = 1;
if (lean::is_scalar(x_40)) {
 x_210 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_210 = x_40;
}
lean::cnstr_set(x_210, 0, x_208);
lean::cnstr_set(x_210, 1, x_34);
lean::cnstr_set(x_210, 2, x_36);
lean::cnstr_set(x_210, 3, x_38);
lean::cnstr_set_scalar(x_210, sizeof(void*)*4, x_209);
x_211 = x_210;
return x_211;
}
else
{
uint8 x_212; 
x_212 = lean::cnstr_get_scalar<uint8>(x_199, sizeof(void*)*4);
if (x_212 == 0)
{
obj* x_213; obj* x_215; obj* x_217; obj* x_218; obj* x_220; obj* x_222; obj* x_224; obj* x_226; uint8 x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_213 = lean::cnstr_get(x_192, 1);
x_215 = lean::cnstr_get(x_192, 2);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 3);
 x_217 = x_192;
} else {
 lean::inc(x_213);
 lean::inc(x_215);
 lean::dec(x_192);
 x_217 = lean::box(0);
}
x_218 = lean::cnstr_get(x_199, 0);
x_220 = lean::cnstr_get(x_199, 1);
x_222 = lean::cnstr_get(x_199, 2);
x_224 = lean::cnstr_get(x_199, 3);
if (lean::is_exclusive(x_199)) {
 x_226 = x_199;
} else {
 lean::inc(x_218);
 lean::inc(x_220);
 lean::inc(x_222);
 lean::inc(x_224);
 lean::dec(x_199);
 x_226 = lean::box(0);
}
x_227 = 1;
if (lean::is_scalar(x_226)) {
 x_228 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_228 = x_226;
}
lean::cnstr_set(x_228, 0, x_197);
lean::cnstr_set(x_228, 1, x_213);
lean::cnstr_set(x_228, 2, x_215);
lean::cnstr_set(x_228, 3, x_218);
lean::cnstr_set_scalar(x_228, sizeof(void*)*4, x_227);
x_229 = x_228;
if (lean::is_scalar(x_217)) {
 x_230 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_230 = x_217;
}
lean::cnstr_set(x_230, 0, x_224);
lean::cnstr_set(x_230, 1, x_34);
lean::cnstr_set(x_230, 2, x_36);
lean::cnstr_set(x_230, 3, x_38);
lean::cnstr_set_scalar(x_230, sizeof(void*)*4, x_227);
x_231 = x_230;
if (lean::is_scalar(x_40)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_40;
}
lean::cnstr_set(x_232, 0, x_229);
lean::cnstr_set(x_232, 1, x_220);
lean::cnstr_set(x_232, 2, x_222);
lean::cnstr_set(x_232, 3, x_231);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_212);
x_233 = x_232;
return x_233;
}
else
{
obj* x_234; obj* x_236; obj* x_238; uint8 x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
x_234 = lean::cnstr_get(x_192, 1);
x_236 = lean::cnstr_get(x_192, 2);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 3);
 x_238 = x_192;
} else {
 lean::inc(x_234);
 lean::inc(x_236);
 lean::dec(x_192);
 x_238 = lean::box(0);
}
x_239 = 0;
if (lean::is_scalar(x_238)) {
 x_240 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_240 = x_238;
}
lean::cnstr_set(x_240, 0, x_197);
lean::cnstr_set(x_240, 1, x_234);
lean::cnstr_set(x_240, 2, x_236);
lean::cnstr_set(x_240, 3, x_199);
lean::cnstr_set_scalar(x_240, sizeof(void*)*4, x_239);
x_241 = x_240;
if (lean::is_scalar(x_40)) {
 x_242 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_242 = x_40;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_34);
lean::cnstr_set(x_242, 2, x_36);
lean::cnstr_set(x_242, 3, x_38);
lean::cnstr_set_scalar(x_242, sizeof(void*)*4, x_212);
x_243 = x_242;
return x_243;
}
}
}
else
{
uint8 x_244; 
x_244 = lean::cnstr_get_scalar<uint8>(x_197, sizeof(void*)*4);
if (x_244 == 0)
{
obj* x_245; obj* x_247; obj* x_249; obj* x_251; obj* x_252; obj* x_254; obj* x_256; obj* x_258; obj* x_260; uint8 x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; 
x_245 = lean::cnstr_get(x_192, 1);
x_247 = lean::cnstr_get(x_192, 2);
x_249 = lean::cnstr_get(x_192, 3);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 x_251 = x_192;
} else {
 lean::inc(x_245);
 lean::inc(x_247);
 lean::inc(x_249);
 lean::dec(x_192);
 x_251 = lean::box(0);
}
x_252 = lean::cnstr_get(x_197, 0);
x_254 = lean::cnstr_get(x_197, 1);
x_256 = lean::cnstr_get(x_197, 2);
x_258 = lean::cnstr_get(x_197, 3);
if (lean::is_exclusive(x_197)) {
 x_260 = x_197;
} else {
 lean::inc(x_252);
 lean::inc(x_254);
 lean::inc(x_256);
 lean::inc(x_258);
 lean::dec(x_197);
 x_260 = lean::box(0);
}
x_261 = 1;
if (lean::is_scalar(x_260)) {
 x_262 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_262 = x_260;
}
lean::cnstr_set(x_262, 0, x_252);
lean::cnstr_set(x_262, 1, x_254);
lean::cnstr_set(x_262, 2, x_256);
lean::cnstr_set(x_262, 3, x_258);
lean::cnstr_set_scalar(x_262, sizeof(void*)*4, x_261);
x_263 = x_262;
if (lean::is_scalar(x_251)) {
 x_264 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_264 = x_251;
}
lean::cnstr_set(x_264, 0, x_249);
lean::cnstr_set(x_264, 1, x_34);
lean::cnstr_set(x_264, 2, x_36);
lean::cnstr_set(x_264, 3, x_38);
lean::cnstr_set_scalar(x_264, sizeof(void*)*4, x_261);
x_265 = x_264;
if (lean::is_scalar(x_40)) {
 x_266 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_266 = x_40;
}
lean::cnstr_set(x_266, 0, x_263);
lean::cnstr_set(x_266, 1, x_245);
lean::cnstr_set(x_266, 2, x_247);
lean::cnstr_set(x_266, 3, x_265);
lean::cnstr_set_scalar(x_266, sizeof(void*)*4, x_244);
x_267 = x_266;
return x_267;
}
else
{
obj* x_268; 
x_268 = lean::cnstr_get(x_192, 3);
lean::inc(x_268);
if (lean::obj_tag(x_268) == 0)
{
obj* x_270; obj* x_272; obj* x_274; uint8 x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
x_270 = lean::cnstr_get(x_192, 1);
x_272 = lean::cnstr_get(x_192, 2);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 3);
 x_274 = x_192;
} else {
 lean::inc(x_270);
 lean::inc(x_272);
 lean::dec(x_192);
 x_274 = lean::box(0);
}
x_275 = 0;
if (lean::is_scalar(x_274)) {
 x_276 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_276 = x_274;
}
lean::cnstr_set(x_276, 0, x_197);
lean::cnstr_set(x_276, 1, x_270);
lean::cnstr_set(x_276, 2, x_272);
lean::cnstr_set(x_276, 3, x_268);
lean::cnstr_set_scalar(x_276, sizeof(void*)*4, x_275);
x_277 = x_276;
if (lean::is_scalar(x_40)) {
 x_278 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_278 = x_40;
}
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_34);
lean::cnstr_set(x_278, 2, x_36);
lean::cnstr_set(x_278, 3, x_38);
lean::cnstr_set_scalar(x_278, sizeof(void*)*4, x_244);
x_279 = x_278;
return x_279;
}
else
{
uint8 x_280; 
x_280 = lean::cnstr_get_scalar<uint8>(x_268, sizeof(void*)*4);
if (x_280 == 0)
{
obj* x_282; obj* x_284; obj* x_286; obj* x_287; obj* x_289; obj* x_291; obj* x_293; obj* x_295; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_40);
x_282 = lean::cnstr_get(x_192, 1);
x_284 = lean::cnstr_get(x_192, 2);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 3);
 x_286 = x_192;
} else {
 lean::inc(x_282);
 lean::inc(x_284);
 lean::dec(x_192);
 x_286 = lean::box(0);
}
x_287 = lean::cnstr_get(x_268, 0);
x_289 = lean::cnstr_get(x_268, 1);
x_291 = lean::cnstr_get(x_268, 2);
x_293 = lean::cnstr_get(x_268, 3);
if (lean::is_exclusive(x_268)) {
 x_295 = x_268;
} else {
 lean::inc(x_287);
 lean::inc(x_289);
 lean::inc(x_291);
 lean::inc(x_293);
 lean::dec(x_268);
 x_295 = lean::box(0);
}
lean::inc(x_197);
if (lean::is_scalar(x_295)) {
 x_297 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_297 = x_295;
}
lean::cnstr_set(x_297, 0, x_197);
lean::cnstr_set(x_297, 1, x_282);
lean::cnstr_set(x_297, 2, x_284);
lean::cnstr_set(x_297, 3, x_287);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 lean::cnstr_release(x_197, 2);
 lean::cnstr_release(x_197, 3);
 x_298 = x_197;
} else {
 lean::dec(x_197);
 x_298 = lean::box(0);
}
lean::cnstr_set_scalar(x_297, sizeof(void*)*4, x_244);
x_299 = x_297;
if (lean::is_scalar(x_298)) {
 x_300 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_300 = x_298;
}
lean::cnstr_set(x_300, 0, x_293);
lean::cnstr_set(x_300, 1, x_34);
lean::cnstr_set(x_300, 2, x_36);
lean::cnstr_set(x_300, 3, x_38);
lean::cnstr_set_scalar(x_300, sizeof(void*)*4, x_244);
x_301 = x_300;
if (lean::is_scalar(x_286)) {
 x_302 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_302 = x_286;
}
lean::cnstr_set(x_302, 0, x_299);
lean::cnstr_set(x_302, 1, x_289);
lean::cnstr_set(x_302, 2, x_291);
lean::cnstr_set(x_302, 3, x_301);
lean::cnstr_set_scalar(x_302, sizeof(void*)*4, x_280);
x_303 = x_302;
return x_303;
}
else
{
obj* x_304; obj* x_306; obj* x_308; obj* x_309; obj* x_311; obj* x_313; obj* x_315; obj* x_317; obj* x_318; obj* x_319; uint8 x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; 
x_304 = lean::cnstr_get(x_192, 1);
x_306 = lean::cnstr_get(x_192, 2);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 3);
 x_308 = x_192;
} else {
 lean::inc(x_304);
 lean::inc(x_306);
 lean::dec(x_192);
 x_308 = lean::box(0);
}
x_309 = lean::cnstr_get(x_197, 0);
x_311 = lean::cnstr_get(x_197, 1);
x_313 = lean::cnstr_get(x_197, 2);
x_315 = lean::cnstr_get(x_197, 3);
if (lean::is_exclusive(x_197)) {
 x_317 = x_197;
} else {
 lean::inc(x_309);
 lean::inc(x_311);
 lean::inc(x_313);
 lean::inc(x_315);
 lean::dec(x_197);
 x_317 = lean::box(0);
}
if (lean::is_scalar(x_317)) {
 x_318 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_318 = x_317;
}
lean::cnstr_set(x_318, 0, x_309);
lean::cnstr_set(x_318, 1, x_311);
lean::cnstr_set(x_318, 2, x_313);
lean::cnstr_set(x_318, 3, x_315);
lean::cnstr_set_scalar(x_318, sizeof(void*)*4, x_280);
x_319 = x_318;
x_320 = 0;
if (lean::is_scalar(x_308)) {
 x_321 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_321 = x_308;
}
lean::cnstr_set(x_321, 0, x_319);
lean::cnstr_set(x_321, 1, x_304);
lean::cnstr_set(x_321, 2, x_306);
lean::cnstr_set(x_321, 3, x_268);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_320);
x_322 = x_321;
if (lean::is_scalar(x_40)) {
 x_323 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_323 = x_40;
}
lean::cnstr_set(x_323, 0, x_322);
lean::cnstr_set(x_323, 1, x_34);
lean::cnstr_set(x_323, 2, x_36);
lean::cnstr_set(x_323, 3, x_38);
lean::cnstr_set_scalar(x_323, sizeof(void*)*4, x_280);
x_324 = x_323;
return x_324;
}
}
}
}
}
}
}
}
}
}
}
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
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
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_4, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
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
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_22; uint8 x_23; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
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
x_18 = lean::cnstr_get(x_7, 2);
lean::inc(x_18);
lean::dec(x_7);
lean::inc(x_1);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__1), 3, 2);
lean::closure_set(x_22, 0, x_5);
lean::closure_set(x_22, 1, x_1);
x_23 = l_RBNode_isRed___main___rarg(x_12);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_24 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_12, x_2, x_17);
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_10);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_18);
lean::cnstr_set(x_25, 3, x_14);
x_26 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_9;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean::apply_2(x_1, lean::box(0), x_27);
x_29 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_28, x_22);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = l_RBNode_ins___main___at_Lean_Trace_Lean_Trace_MonadTracer___spec__1(x_12, x_2, x_17);
x_31 = l_RBNode_setBlack___main___rarg(x_30);
x_32 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_32, 0, x_10);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set(x_32, 2, x_18);
lean::cnstr_set(x_32, 3, x_14);
x_33 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_9;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::apply_2(x_1, lean::box(0), x_34);
x_36 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_35, x_22);
return x_36;
}
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::thunk_get_own(x_0);
x_10 = lean::apply_1(x_9, x_6);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__2), 5, 4);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_2);
lean::closure_set(x_12, 2, x_3);
lean::closure_set(x_12, 3, x_4);
x_13 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; uint8 x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_15 = 0;
x_16 = l_Lean_KVMap_getBool(x_12, x_0, x_15);
if (x_16 == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_22 = lean::thunk_get_own(x_1);
lean::dec(x_1);
x_24 = lean::apply_1(x_22, x_9);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
x_25 = lean::cnstr_get(x_9, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_9, 1);
lean::inc(x_27);
lean::dec(x_9);
lean::inc(x_2);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_2);
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_33, 0, x_25);
lean::cnstr_set(x_33, 1, x_27);
lean::cnstr_set(x_33, 2, x_31);
lean::cnstr_set(x_33, 3, x_32);
x_34 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
lean::inc(x_3);
x_37 = lean::apply_2(x_3, lean::box(0), x_35);
lean::inc(x_5);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__3___boxed), 6, 5);
lean::closure_set(x_39, 0, x_1);
lean::closure_set(x_39, 1, x_4);
lean::closure_set(x_39, 2, x_3);
lean::closure_set(x_39, 3, x_2);
lean::closure_set(x_39, 4, x_5);
x_40 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_37, x_39);
return x_40;
}
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
lean::inc(x_6);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_6);
lean::inc(x_12);
x_18 = lean::apply_2(x_12, lean::box(0), x_16);
lean::inc(x_7);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__4___boxed), 7, 6);
lean::closure_set(x_20, 0, x_3);
lean::closure_set(x_20, 1, x_5);
lean::closure_set(x_20, 2, x_2);
lean::closure_set(x_20, 3, x_12);
lean::closure_set(x_20, 4, x_4);
lean::closure_set(x_20, 5, x_7);
x_21 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_18, x_20);
return x_21;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::box(0);
x_6 = lean::cnstr_get(x_0, 3);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set(x_9, 2, x_5);
lean::cnstr_set(x_9, 3, x_6);
return x_9;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__7(obj* x_0, obj* x_1) {
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
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
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
x_25 = l_List_append___rarg(x_17, x_24);
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
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__1), 3, 2);
lean::closure_set(x_31, 0, x_6);
lean::closure_set(x_31, 1, x_3);
x_32 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_30, x_31);
return x_32;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::thunk_get_own(x_0);
x_11 = lean::apply_1(x_10, x_7);
lean::inc(x_5);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__8), 6, 5);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_4);
lean::closure_set(x_13, 4, x_5);
x_14 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_17; obj* x_20; obj* x_22; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
x_20 = lean::thunk_get_own(x_0);
lean::dec(x_0);
x_22 = lean::apply_1(x_20, x_17);
return x_22;
}
else
{
obj* x_24; obj* x_26; obj* x_27; uint8 x_29; uint8 x_31; 
lean::dec(x_9);
x_24 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_26 = x_8;
} else {
 lean::inc(x_24);
 lean::dec(x_8);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_29 = 0;
lean::inc(x_27);
x_31 = l_Lean_KVMap_getBool(x_27, x_2, x_29);
if (x_31 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_5);
lean::dec(x_26);
lean::dec(x_7);
lean::dec(x_6);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__6___boxed), 3, 2);
lean::closure_set(x_36, 0, x_1);
lean::closure_set(x_36, 1, x_27);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__7), 2, 1);
lean::closure_set(x_37, 0, x_3);
x_38 = lean::thunk_get_own(x_0);
lean::dec(x_0);
x_40 = l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg(x_4, lean::box(0), x_36, x_37, x_38, x_24);
return x_40;
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_4);
lean::dec(x_24);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
x_45 = lean::box(0);
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_27);
lean::cnstr_set(x_46, 1, x_43);
lean::cnstr_set(x_46, 2, x_3);
lean::cnstr_set(x_46, 3, x_45);
x_47 = lean::box(0);
if (lean::is_scalar(x_26)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_26;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_46);
lean::inc(x_5);
x_50 = lean::apply_2(x_5, lean::box(0), x_48);
lean::inc(x_7);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__9___boxed), 7, 6);
lean::closure_set(x_52, 0, x_0);
lean::closure_set(x_52, 1, x_1);
lean::closure_set(x_52, 2, x_6);
lean::closure_set(x_52, 3, x_45);
lean::closure_set(x_52, 4, x_5);
lean::closure_set(x_52, 5, x_7);
x_53 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_50, x_52);
return x_53;
}
}
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
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
lean::inc(x_5);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__10___boxed), 9, 8);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_7);
lean::closure_set(x_19, 2, x_2);
lean::closure_set(x_19, 3, x_12);
lean::closure_set(x_19, 4, x_3);
lean::closure_set(x_19, 5, x_0);
lean::closure_set(x_19, 6, x_4);
lean::closure_set(x_19, 7, x_5);
x_20 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_17, x_19);
return x_20;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
lean::inc(x_5);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_5);
lean::inc(x_10);
x_16 = lean::apply_2(x_10, lean::box(0), x_14);
lean::inc(x_6);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__11), 7, 6);
lean::closure_set(x_18, 0, x_10);
lean::closure_set(x_18, 1, x_4);
lean::closure_set(x_18, 2, x_2);
lean::closure_set(x_18, 3, x_0);
lean::closure_set(x_18, 4, x_3);
lean::closure_set(x_18, 5, x_6);
x_19 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_16, x_18);
return x_19;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__5___boxed), 7, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__12___boxed), 6, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_Lean_Trace_MonadTracer___rarg), 1, 0);
return x_1;
}
}
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_MonadStateAdapter_adaptState_x_27___at_Lean_Trace_Lean_Trace_MonadTracer___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__3(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
return x_7;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__5(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__6(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__9(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
return x_7;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__10(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_2);
return x_9;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Trace_Lean_Trace_MonadTracer___rarg___lambda__12(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Trace_Lean_Trace_MonadTracer___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Trace_Lean_Trace_MonadTracer(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Trace_TraceT_run___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
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
obj* l_Lean_Trace_TraceT_run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::box(0);
x_6 = lean::box(0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_6);
lean::cnstr_set(x_8, 3, x_7);
x_9 = lean::apply_1(x_2, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_TraceT_run___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_0);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Trace_TraceT_run(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Trace_TraceT_run___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Trace_TraceT_run___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Trace_TraceT_run(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_lean_format(obj*);
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_lean_position(obj*);
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_options(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_trace(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_position(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_options(w);
if (io_result_is_error(w)) return w;
return w;
}
