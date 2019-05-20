// Lean compiler output
// Module: init.lean.compiler.ir.emitutil
// Imports: init.control.conditional init.lean.compiler.ir.compilerm
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
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace___main(obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace___boxed(obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_findEnvDecl(obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
uint8 l_Lean_Name_isPrefixOf___main(obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace___main___boxed(obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
obj* _init_l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_17; 
x_11 = lean::array_fget(x_0, x_1);
x_12 = l_Lean_IR_AltCore_body___main(x_11);
lean::dec(x_11);
x_14 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_12, x_2, x_3);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
lean::dec(x_14);
x_21 = lean::mk_nat_obj(1ul);
x_22 = lean::nat_add(x_1, x_21);
lean::dec(x_1);
x_1 = x_22;
x_3 = x_18;
goto _start;
}
else
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_28 = x_14;
} else {
 lean::inc(x_26);
 lean::dec(x_14);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
switch (lean::obj_tag(x_5)) {
case 6:
{
obj* x_7; obj* x_10; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_14 = l_Lean_Name_isPrefixOf___main(x_13, x_10);
if (x_14 == 0)
{
uint8 x_16; 
lean::inc(x_2);
x_16 = l_Lean_NameSet_contains(x_2, x_10);
if (x_16 == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::box(0);
lean::inc(x_10);
x_19 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_10, x_17);
x_20 = l_Lean_IR_findEnvDecl(x_1, x_10);
lean::dec(x_10);
if (lean::obj_tag(x_20) == 0)
{
x_0 = x_7;
x_2 = x_19;
goto _start;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_29; obj* x_30; uint8 x_32; 
x_26 = lean::cnstr_get(x_23, 2);
lean::inc(x_26);
lean::dec(x_23);
x_29 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_26, x_1, x_19);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::unbox(x_30);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_0 = x_7;
x_2 = x_33;
goto _start;
}
else
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_7);
x_38 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_40 = x_29;
} else {
 lean::inc(x_38);
 lean::dec(x_29);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean::dec(x_23);
x_0 = x_7;
x_2 = x_19;
goto _start;
}
}
}
else
{
lean::dec(x_10);
x_0 = x_7;
goto _start;
}
}
else
{
uint8 x_48; obj* x_49; obj* x_50; 
lean::dec(x_7);
lean::dec(x_10);
x_48 = 1;
x_49 = lean::box(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_2);
return x_50;
}
}
case 7:
{
obj* x_51; obj* x_54; obj* x_57; uint8 x_58; 
x_51 = lean::cnstr_get(x_0, 2);
lean::inc(x_51);
lean::dec(x_0);
x_54 = lean::cnstr_get(x_5, 0);
lean::inc(x_54);
lean::dec(x_5);
x_57 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_58 = l_Lean_Name_isPrefixOf___main(x_57, x_54);
if (x_58 == 0)
{
uint8 x_60; 
lean::inc(x_2);
x_60 = l_Lean_NameSet_contains(x_2, x_54);
if (x_60 == 0)
{
obj* x_61; obj* x_63; obj* x_64; 
x_61 = lean::box(0);
lean::inc(x_54);
x_63 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_54, x_61);
x_64 = l_Lean_IR_findEnvDecl(x_1, x_54);
lean::dec(x_54);
if (lean::obj_tag(x_64) == 0)
{
x_0 = x_51;
x_2 = x_63;
goto _start;
}
else
{
obj* x_67; 
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
if (lean::obj_tag(x_67) == 0)
{
obj* x_70; obj* x_73; obj* x_74; uint8 x_76; 
x_70 = lean::cnstr_get(x_67, 2);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_70, x_1, x_63);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::unbox(x_74);
if (x_76 == 0)
{
obj* x_77; 
x_77 = lean::cnstr_get(x_73, 1);
lean::inc(x_77);
lean::dec(x_73);
x_0 = x_51;
x_2 = x_77;
goto _start;
}
else
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_51);
x_82 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_84 = x_73;
} else {
 lean::inc(x_82);
 lean::dec(x_73);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_74);
lean::cnstr_set(x_85, 1, x_82);
return x_85;
}
}
else
{
lean::dec(x_67);
x_0 = x_51;
x_2 = x_63;
goto _start;
}
}
}
else
{
lean::dec(x_54);
x_0 = x_51;
goto _start;
}
}
else
{
uint8 x_92; obj* x_93; obj* x_94; 
lean::dec(x_54);
lean::dec(x_51);
x_92 = 1;
x_93 = lean::box(x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_2);
return x_94;
}
}
default:
{
obj* x_96; 
lean::dec(x_5);
x_96 = lean::cnstr_get(x_0, 2);
lean::inc(x_96);
lean::dec(x_0);
x_0 = x_96;
goto _start;
}
}
}
case 1:
{
obj* x_100; obj* x_102; obj* x_105; obj* x_106; uint8 x_108; 
x_100 = lean::cnstr_get(x_0, 2);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_0, 3);
lean::inc(x_102);
lean::dec(x_0);
x_105 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_100, x_1, x_2);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::unbox(x_106);
if (x_108 == 0)
{
obj* x_109; 
x_109 = lean::cnstr_get(x_105, 1);
lean::inc(x_109);
lean::dec(x_105);
x_0 = x_102;
x_2 = x_109;
goto _start;
}
else
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_102);
x_114 = lean::cnstr_get(x_105, 1);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 x_116 = x_105;
} else {
 lean::inc(x_114);
 lean::dec(x_105);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_106);
lean::cnstr_set(x_117, 1, x_114);
return x_117;
}
}
case 9:
{
obj* x_118; obj* x_121; obj* x_122; 
x_118 = lean::cnstr_get(x_0, 2);
lean::inc(x_118);
lean::dec(x_0);
x_121 = lean::mk_nat_obj(0ul);
x_122 = l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_118, x_121, x_1, x_2);
lean::dec(x_118);
return x_122;
}
default:
{
obj* x_124; 
x_124 = lean::box(0);
x_3 = x_124;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_126; 
lean::dec(x_3);
x_126 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_126 == 0)
{
obj* x_127; 
x_127 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_127;
goto _start;
}
else
{
uint8 x_131; obj* x_132; obj* x_133; 
lean::dec(x_0);
x_131 = 0;
x_132 = lean::box(x_131);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_2);
return x_133;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UsesLeanNamespace_visitFnBody(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_usesLeanNamespace___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_2, x_0, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
else
{
uint8 x_11; obj* x_12; 
lean::dec(x_1);
x_11 = 0;
x_12 = lean::box(x_11);
return x_12;
}
}
}
obj* l_Lean_IR_usesLeanNamespace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_usesLeanNamespace___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_usesLeanNamespace(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_usesLeanNamespace___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_usesLeanNamespace___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_usesLeanNamespace(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* initialize_init_control_conditional(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_emitutil(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix = _init_l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix();
lean::mark_persistent(l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix);
return w;
}
