// Lean compiler output
// Module: init.lean.compiler.ir.livevars
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.freevars init.control.reader init.control.conditional
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
obj* l_Lean_IR_IsLive_visitArgs___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_getJPBody(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitExpr___main(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitArg(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitExpr___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitVar___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_hasLiveVar___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_IsLive_visitFnBody___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_hasLiveVar(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitJP___boxed(obj*, obj*, obj*);
obj* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_IsLive_visitFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitExpr(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_IsLive_visitJP(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitArgs(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_IsLive_visitFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitFnBody___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitVar(obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitArg___main(obj*, obj*);
obj* l_Lean_IR_IsLive_visitArg___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_IsLive_visitVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = lean::nat_dec_eq(x_0, x_1);
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_Lean_IR_IsLive_visitVar___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitVar(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_IsLive_visitJP(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = lean::nat_dec_eq(x_0, x_1);
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_Lean_IR_IsLive_visitJP___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitJP(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_IsLive_visitArg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_1);
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_Lean_IR_IsLive_visitArg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitArg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_IsLive_visitArgs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_1, x_3);
x_5 = lean::box(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
obj* l_Lean_IR_IsLive_visitArgs___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitArgs(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_IsLive_visitExpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_IR_HasIndex_visitExpr___main(x_0, x_1);
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_Lean_IR_IsLive_visitExpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitExpr(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_IsLive_visitFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_8; obj* x_9; obj* x_10; 
lean::dec(x_2);
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
x_11 = lean::array_fget(x_1, x_2);
x_12 = l_Lean_IR_AltCore_body___main(x_11);
lean::dec(x_11);
x_14 = l_Lean_IR_IsLive_visitFnBody___main(x_0, x_12, x_3);
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
x_22 = lean::nat_add(x_2, x_21);
lean::dec(x_2);
x_2 = x_22;
x_3 = x_18;
goto _start;
}
else
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_2);
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
obj* l_Lean_IR_IsLive_visitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_5; uint8 x_8; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_Lean_IR_HasIndex_visitExpr___main(x_0, x_3);
lean::dec(x_3);
if (x_8 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_5);
x_12 = lean::box(x_8);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_2);
return x_13;
}
}
case 1:
{
obj* x_14; obj* x_16; obj* x_19; obj* x_20; uint8 x_22; 
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
lean::dec(x_1);
x_19 = l_Lean_IR_IsLive_visitFnBody___main(x_0, x_14, x_2);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::unbox(x_20);
if (x_22 == 0)
{
obj* x_23; 
x_23 = lean::cnstr_get(x_19, 1);
lean::inc(x_23);
lean::dec(x_19);
x_1 = x_16;
x_2 = x_23;
goto _start;
}
else
{
obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_16);
x_28 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_30 = x_19;
} else {
 lean::inc(x_28);
 lean::dec(x_19);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
}
case 2:
{
obj* x_32; obj* x_34; obj* x_36; uint8 x_39; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_1, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_1, 3);
lean::inc(x_36);
lean::dec(x_1);
x_39 = lean::nat_dec_eq(x_0, x_32);
lean::dec(x_32);
if (x_39 == 0)
{
uint8 x_41; 
x_41 = lean::nat_dec_eq(x_0, x_34);
lean::dec(x_34);
if (x_41 == 0)
{
x_1 = x_36;
goto _start;
}
else
{
obj* x_45; obj* x_46; 
lean::dec(x_36);
x_45 = lean::box(x_41);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_2);
return x_46;
}
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_34);
lean::dec(x_36);
x_49 = lean::box(x_39);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_2);
return x_50;
}
}
case 3:
{
obj* x_51; obj* x_53; obj* x_55; uint8 x_58; 
x_51 = lean::cnstr_get(x_1, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_1, 2);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_1, 3);
lean::inc(x_55);
lean::dec(x_1);
x_58 = lean::nat_dec_eq(x_0, x_51);
lean::dec(x_51);
if (x_58 == 0)
{
uint8 x_60; 
x_60 = lean::nat_dec_eq(x_0, x_53);
lean::dec(x_53);
if (x_60 == 0)
{
x_1 = x_55;
goto _start;
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_55);
x_64 = lean::box(x_60);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_2);
return x_65;
}
}
else
{
obj* x_68; obj* x_69; 
lean::dec(x_53);
lean::dec(x_55);
x_68 = lean::box(x_58);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_2);
return x_69;
}
}
case 4:
{
obj* x_70; obj* x_72; obj* x_74; uint8 x_77; 
x_70 = lean::cnstr_get(x_1, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_1, 3);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_1, 4);
lean::inc(x_74);
lean::dec(x_1);
x_77 = lean::nat_dec_eq(x_0, x_70);
lean::dec(x_70);
if (x_77 == 0)
{
uint8 x_79; 
x_79 = lean::nat_dec_eq(x_0, x_72);
lean::dec(x_72);
if (x_79 == 0)
{
x_1 = x_74;
goto _start;
}
else
{
obj* x_83; obj* x_84; 
lean::dec(x_74);
x_83 = lean::box(x_79);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_2);
return x_84;
}
}
else
{
obj* x_87; obj* x_88; 
lean::dec(x_74);
lean::dec(x_72);
x_87 = lean::box(x_77);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_2);
return x_88;
}
}
case 8:
{
obj* x_89; 
x_89 = lean::cnstr_get(x_1, 1);
lean::inc(x_89);
lean::dec(x_1);
x_1 = x_89;
goto _start;
}
case 9:
{
obj* x_93; obj* x_95; uint8 x_98; 
x_93 = lean::cnstr_get(x_1, 1);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_1, 2);
lean::inc(x_95);
lean::dec(x_1);
x_98 = lean::nat_dec_eq(x_0, x_93);
lean::dec(x_93);
if (x_98 == 0)
{
obj* x_100; obj* x_101; 
x_100 = lean::mk_nat_obj(0ul);
x_101 = l_Array_anyMAux___main___at_Lean_IR_IsLive_visitFnBody___main___spec__1(x_0, x_95, x_100, x_2);
lean::dec(x_95);
return x_101;
}
else
{
obj* x_104; obj* x_105; 
lean::dec(x_95);
x_104 = lean::box(x_98);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_2);
return x_105;
}
}
case 10:
{
obj* x_106; uint8 x_109; obj* x_111; obj* x_112; 
x_106 = lean::cnstr_get(x_1, 0);
lean::inc(x_106);
lean::dec(x_1);
x_109 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_106);
lean::dec(x_106);
x_111 = lean::box(x_109);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_2);
return x_112;
}
case 11:
{
obj* x_113; obj* x_115; obj* x_118; uint8 x_119; 
x_113 = lean::cnstr_get(x_1, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_1, 1);
lean::inc(x_115);
lean::dec(x_1);
x_118 = lean::mk_nat_obj(0ul);
x_119 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_115, x_118);
lean::dec(x_115);
if (x_119 == 0)
{
obj* x_122; 
lean::inc(x_2);
x_122 = l_Lean_IR_LocalContext_getJPBody(x_2, x_113);
if (lean::obj_tag(x_122) == 0)
{
obj* x_124; obj* x_125; 
lean::dec(x_113);
x_124 = lean::box(x_119);
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_2);
return x_125;
}
else
{
obj* x_126; obj* x_129; 
x_126 = lean::cnstr_get(x_122, 0);
lean::inc(x_126);
lean::dec(x_122);
x_129 = l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_113, x_2);
lean::dec(x_113);
x_1 = x_126;
x_2 = x_129;
goto _start;
}
}
else
{
obj* x_133; obj* x_134; 
lean::dec(x_113);
x_133 = lean::box(x_119);
x_134 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_2);
return x_134;
}
}
case 12:
{
uint8 x_135; obj* x_136; obj* x_137; 
x_135 = 0;
x_136 = lean::box(x_135);
x_137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_2);
return x_137;
}
default:
{
obj* x_138; obj* x_140; uint8 x_143; 
x_138 = lean::cnstr_get(x_1, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_1, 2);
lean::inc(x_140);
lean::dec(x_1);
x_143 = lean::nat_dec_eq(x_0, x_138);
lean::dec(x_138);
if (x_143 == 0)
{
x_1 = x_140;
goto _start;
}
else
{
obj* x_147; obj* x_148; 
lean::dec(x_140);
x_147 = lean::box(x_143);
x_148 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_2);
return x_148;
}
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_IsLive_visitFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_IsLive_visitFnBody___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_IsLive_visitFnBody___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitFnBody___main(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_IsLive_visitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_IsLive_visitFnBody___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_IsLive_visitFnBody(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_FnBody_hasLiveVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_IR_IsLive_visitFnBody___main(x_2, x_0, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_FnBody_hasLiveVar___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_FnBody_hasLiveVar(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_freevars(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_control_conditional(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_livevars(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (io_result_is_error(w)) return w;
return w;
}
