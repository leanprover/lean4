// Lean compiler output
// Module: init.lean.compiler.ir.format
// Imports: init.lean.compiler.ir.basic init.lean.format
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
obj* l_Lean_IR_formatDecl(obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__20;
obj* l_Lean_IR_formatAlt(obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_formatKVMap(obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3;
extern obj* l_Lean_Format_paren___closed__2;
extern obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Lean_IR_formatDecl___main(obj*, obj*);
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(obj*);
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4;
obj* l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main(uint8);
obj* l_Lean_IR_formatParams___boxed(obj*);
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___boxed(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__6;
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1;
namespace lean {
namespace ir {
obj* decl_to_string_core(obj*);
}
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__17;
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_IR_formatAlt___main___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__13;
obj* l_Lean_IR_declHasFormat;
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Format_join___closed__1;
obj* l___private_init_lean_compiler_ir_format_1__formatArg(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__11;
obj* l___private_init_lean_compiler_ir_format_7__formatParam(obj*);
obj* l_Lean_IR_formatAlt___main(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__12;
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_IR_formatFnBody___main___closed__15;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___boxed(obj*);
obj* l_Lean_IR_argHasFormat;
obj* l_Lean_IR_typeHasFormat;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8;
obj* l_Lean_IR_formatFnBody___main___closed__8;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8;
obj* l_Lean_IR_fnBodyHasFormat;
obj* l___private_init_lean_compiler_ir_format_1__formatArg___main(obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__3;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal___main(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__9;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2;
obj* l_Array_fget(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_IR_formatDecl___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1;
extern obj* l_Lean_formatEntry___main___closed__1;
obj* l_Lean_IR_formatFnBody___main___closed__14;
obj* l_Lean_IR_formatFnBody___main___closed__2;
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal(obj*);
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12;
extern obj* l_Lean_Format_flatten___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__19;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1___boxed(obj*);
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2;
obj* l_Lean_IR_declHasToString;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType(uint8);
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5;
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11;
obj* l_Lean_IR_formatFnBody___main___closed__10;
extern obj* l_Lean_Format_sbracket___closed__3;
obj* l_Lean_IR_formatFnBody___main___closed__5;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody(obj*, obj*);
obj* l_Lean_IR_ctorInfoHasFormat;
extern obj* l_Lean_formatKVMap___closed__1;
obj* l_Lean_IR_formatDecl___main___closed__2;
obj* l_Lean_IR_formatFnBody___main___closed__16;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1___boxed(obj*);
obj* l_Lean_IR_exprHasToString(obj*);
obj* l___private_init_lean_compiler_ir_format_2__formatArray(obj*);
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo(obj*);
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(obj*);
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
obj* l_Array_size(obj*, obj*);
obj* l_Lean_IR_exprHasFormat;
obj* l_Lean_IR_formatParams(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__18;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5;
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg(obj*, obj*);
obj* l_Lean_IR_litValHasFormat;
obj* l_Lean_IR_fnBodyHasToString(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
obj* l_Lean_IR_formatAlt___main___closed__2;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1(obj*);
obj* l_String_quote(obj*);
obj* l_Lean_IR_paramHasFormat;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14;
obj* l_Lean_IR_formatFnBody___main___closed__7;
obj* l_Lean_IR_formatFnBody___main___closed__4;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6;
obj* l_Lean_IR_formatFnBody___main(obj*, obj*);
obj* _init_l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("◾");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_1__formatArg___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_IR_VarId_HasToString___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; 
x_7 = l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1;
return x_7;
}
}
}
obj* l___private_init_lean_compiler_ir_format_1__formatArg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_argHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_1__formatArg), 1, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = 0;
x_10 = l_Lean_Format_flatten___main___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
lean::inc(x_1);
x_12 = lean::apply_1(x_1, x_8);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_9);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::box(0);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(x_1, x_2, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_2__formatArray___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_format_2__formatArray___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_quote(x_5);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
}
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_3__formatLitVal___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_litValHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_3__formatLitVal), 1, 0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("ctor_");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(".");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; uint8 x_14; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 3);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 4);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Nat_repr(x_3);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = 0;
x_9 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::nat_dec_lt(x_11, x_4);
x_13 = lean::box(0);
x_14 = lean_name_dec_eq(x_2, x_13);
if (x_12 == 0)
{
uint8 x_15; 
x_15 = lean::nat_dec_lt(x_11, x_5);
if (x_15 == 0)
{
lean::dec(x_5);
lean::dec(x_4);
if (x_14 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_16 = l_Lean_Format_sbracket___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_8);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_2);
x_20 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_8);
x_22 = l_Lean_Format_sbracket___closed__2;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_8);
return x_23;
}
else
{
lean::dec(x_2);
return x_10;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_24 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_10);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_8);
x_26 = l_Nat_repr(x_4);
x_27 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_8);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_24);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_8);
x_30 = l_Nat_repr(x_5);
x_31 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_29);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_8);
if (x_14 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_33 = l_Lean_Format_sbracket___closed__1;
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_8);
x_35 = l_Lean_Name_toString___closed__1;
x_36 = l_Lean_Name_toStringWithSep___main(x_35, x_2);
x_37 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_8);
x_39 = l_Lean_Format_sbracket___closed__2;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_8);
return x_40;
}
else
{
lean::dec(x_2);
return x_32;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_41 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_10);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_8);
x_43 = l_Nat_repr(x_4);
x_44 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_8);
x_46 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_41);
lean::cnstr_set_scalar(x_46, sizeof(void*)*2, x_8);
x_47 = l_Nat_repr(x_5);
x_48 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_8);
if (x_14 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = l_Lean_Format_sbracket___closed__1;
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_50);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_8);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_2);
x_54 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set(x_55, 1, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_8);
x_56 = l_Lean_Format_sbracket___closed__2;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_8);
return x_57;
}
else
{
lean::dec(x_2);
return x_49;
}
}
}
}
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_ctorInfoHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_4__formatCtorInfo), 1, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_7);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_8);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("reset[");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("] ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_string("reuse");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string(" ");
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string("");
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = 0;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" in ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_string("reuse");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string(" ");
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string("!");
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = 0;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("proj[");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("uproj[");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("sproj[");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("pap ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("app ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("box ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("unbox ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("isShared ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("isTaggedPtr ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::box(0);
x_7 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_3, x_3, x_5, x_6);
lean::dec(x_3);
x_8 = 0;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_8);
return x_9;
}
case 1:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
x_12 = l_Nat_repr(x_10);
x_13 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = 0;
x_15 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_14);
x_17 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_14);
x_19 = l_Nat_repr(x_11);
x_20 = l_Lean_IR_VarId_HasToString___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_22 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_14);
return x_23;
}
case 2:
{
obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_27 = lean::cnstr_get(x_1, 2);
lean::inc(x_27);
lean::dec(x_1);
x_28 = l_Nat_repr(x_24);
x_29 = l_Lean_IR_VarId_HasToString___closed__1;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_31 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_25);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::box(0);
x_35 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_27, x_27, x_33, x_34);
lean::dec(x_27);
if (x_26 == 0)
{
uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_36 = 0;
x_37 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3;
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_36);
x_39 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_36);
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_32);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_36);
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_36);
return x_42;
}
else
{
uint8 x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_43 = 0;
x_44 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5;
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_31);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_43);
x_46 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_43);
x_48 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_32);
lean::cnstr_set_scalar(x_48, sizeof(void*)*2, x_43);
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_35);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_43);
return x_49;
}
}
case 3:
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_50 = lean::cnstr_get(x_1, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_1, 1);
lean::inc(x_51);
lean::dec(x_1);
x_52 = l_Nat_repr(x_50);
x_53 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = 0;
x_55 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6;
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_53);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_54);
x_57 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_54);
x_59 = l_Nat_repr(x_51);
x_60 = l_Lean_IR_VarId_HasToString___closed__1;
x_61 = lean::string_append(x_60, x_59);
lean::dec(x_59);
x_62 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_58);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_54);
return x_63;
}
case 4:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_64 = lean::cnstr_get(x_1, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_1, 1);
lean::inc(x_65);
lean::dec(x_1);
x_66 = l_Nat_repr(x_64);
x_67 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = 0;
x_69 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7;
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_67);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_68);
x_71 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_68);
x_73 = l_Nat_repr(x_65);
x_74 = l_Lean_IR_VarId_HasToString___closed__1;
x_75 = lean::string_append(x_74, x_73);
lean::dec(x_73);
x_76 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_72);
lean::cnstr_set(x_77, 1, x_76);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_68);
return x_77;
}
case 5:
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_78 = lean::cnstr_get(x_1, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_1, 1);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_1, 2);
lean::inc(x_80);
lean::dec(x_1);
x_81 = l_Nat_repr(x_78);
x_82 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
x_83 = 0;
x_84 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8;
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_82);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_83);
x_86 = l_Lean_formatKVMap___closed__1;
x_87 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*2, x_83);
x_88 = l_Nat_repr(x_79);
x_89 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set(x_90, 1, x_89);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_83);
x_91 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_92 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*2, x_83);
x_93 = l_Nat_repr(x_80);
x_94 = l_Lean_IR_VarId_HasToString___closed__1;
x_95 = lean::string_append(x_94, x_93);
lean::dec(x_93);
x_96 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
x_97 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_97, 0, x_92);
lean::cnstr_set(x_97, 1, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*2, x_83);
return x_97;
}
case 6:
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; uint8 x_106; obj* x_107; 
x_98 = lean::cnstr_get(x_1, 0);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_1, 1);
lean::inc(x_99);
lean::dec(x_1);
x_100 = l_Lean_Name_toString___closed__1;
x_101 = l_Lean_Name_toStringWithSep___main(x_100, x_98);
x_102 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
x_103 = lean::mk_nat_obj(0u);
x_104 = lean::box(0);
x_105 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_99, x_99, x_103, x_104);
lean::dec(x_99);
x_106 = 0;
x_107 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_107, 0, x_102);
lean::cnstr_set(x_107, 1, x_105);
lean::cnstr_set_scalar(x_107, sizeof(void*)*2, x_106);
return x_107;
}
case 7:
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_108 = lean::cnstr_get(x_1, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_1, 1);
lean::inc(x_109);
lean::dec(x_1);
x_110 = l_Lean_Name_toString___closed__1;
x_111 = l_Lean_Name_toStringWithSep___main(x_110, x_108);
x_112 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_112, 0, x_111);
x_113 = 0;
x_114 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9;
x_115 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_112);
lean::cnstr_set_scalar(x_115, sizeof(void*)*2, x_113);
x_116 = lean::mk_nat_obj(0u);
x_117 = lean::box(0);
x_118 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_109, x_109, x_116, x_117);
lean::dec(x_109);
x_119 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set(x_119, 1, x_118);
lean::cnstr_set_scalar(x_119, sizeof(void*)*2, x_113);
return x_119;
}
case 8:
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; uint8 x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_120 = lean::cnstr_get(x_1, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_1, 1);
lean::inc(x_121);
lean::dec(x_1);
x_122 = l_Nat_repr(x_120);
x_123 = l_Lean_IR_VarId_HasToString___closed__1;
x_124 = lean::string_append(x_123, x_122);
lean::dec(x_122);
x_125 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_125, 0, x_124);
x_126 = 0;
x_127 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10;
x_128 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_125);
lean::cnstr_set_scalar(x_128, sizeof(void*)*2, x_126);
x_129 = lean::mk_nat_obj(0u);
x_130 = lean::box(0);
x_131 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_121, x_121, x_129, x_130);
lean::dec(x_121);
x_132 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_132, 0, x_128);
lean::cnstr_set(x_132, 1, x_131);
lean::cnstr_set_scalar(x_132, sizeof(void*)*2, x_126);
return x_132;
}
case 9:
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; uint8 x_138; obj* x_139; obj* x_140; 
x_133 = lean::cnstr_get(x_1, 0);
lean::inc(x_133);
lean::dec(x_1);
x_134 = l_Nat_repr(x_133);
x_135 = l_Lean_IR_VarId_HasToString___closed__1;
x_136 = lean::string_append(x_135, x_134);
lean::dec(x_134);
x_137 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_137, 0, x_136);
x_138 = 0;
x_139 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11;
x_140 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_137);
lean::cnstr_set_scalar(x_140, sizeof(void*)*2, x_138);
return x_140;
}
case 10:
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; uint8 x_146; obj* x_147; obj* x_148; 
x_141 = lean::cnstr_get(x_1, 0);
lean::inc(x_141);
lean::dec(x_1);
x_142 = l_Nat_repr(x_141);
x_143 = l_Lean_IR_VarId_HasToString___closed__1;
x_144 = lean::string_append(x_143, x_142);
lean::dec(x_142);
x_145 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
x_146 = 0;
x_147 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12;
x_148 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_145);
lean::cnstr_set_scalar(x_148, sizeof(void*)*2, x_146);
return x_148;
}
case 11:
{
obj* x_149; obj* x_150; 
x_149 = lean::cnstr_get(x_1, 0);
lean::inc(x_149);
lean::dec(x_1);
x_150 = l___private_init_lean_compiler_ir_format_3__formatLitVal___main(x_149);
return x_150;
}
case 12:
{
obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; uint8 x_156; obj* x_157; obj* x_158; 
x_151 = lean::cnstr_get(x_1, 0);
lean::inc(x_151);
lean::dec(x_1);
x_152 = l_Nat_repr(x_151);
x_153 = l_Lean_IR_VarId_HasToString___closed__1;
x_154 = lean::string_append(x_153, x_152);
lean::dec(x_152);
x_155 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_155, 0, x_154);
x_156 = 0;
x_157 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13;
x_158 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_155);
lean::cnstr_set_scalar(x_158, sizeof(void*)*2, x_156);
return x_158;
}
default: 
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; uint8 x_164; obj* x_165; obj* x_166; 
x_159 = lean::cnstr_get(x_1, 0);
lean::inc(x_159);
lean::dec(x_1);
x_160 = l_Nat_repr(x_159);
x_161 = l_Lean_IR_VarId_HasToString___closed__1;
x_162 = lean::string_append(x_161, x_160);
lean::dec(x_160);
x_163 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_163, 0, x_162);
x_164 = 0;
x_165 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14;
x_166 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_163);
lean::cnstr_set_scalar(x_166, sizeof(void*)*2, x_164);
return x_166;
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_5__formatExpr___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_exprHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_5__formatExpr), 1, 0);
return x_1;
}
}
obj* l_Lean_IR_exprHasToString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l___private_init_lean_compiler_ir_format_5__formatExpr___main(x_1);
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Format_pretty(x_2, x_3);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("float");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("u8");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("u16");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("u32");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("u64");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("usize");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("obj");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("tobj");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main(uint8 x_1) {
_start:
{
switch (x_1) {
case 0:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2;
return x_3;
}
case 2:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3;
return x_4;
}
case 3:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4;
return x_5;
}
case 4:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5;
return x_6;
}
case 5:
{
obj* x_7; 
x_7 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6;
return x_7;
}
case 6:
{
obj* x_8; 
x_8 = l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1;
return x_8;
}
case 7:
{
obj* x_9; 
x_9 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7;
return x_9;
}
default: 
{
obj* x_10; 
x_10 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8;
return x_10;
}
}
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l___private_init_lean_compiler_ir_format_6__formatIRType(x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_typeHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_6__formatIRType___boxed), 1, 0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" : ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("@& ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1 + 1);
lean::dec(x_1);
x_5 = l_Nat_repr(x_2);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = 0;
x_10 = l_Lean_Format_paren___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_9);
x_14 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_4);
if (x_3 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = l_Lean_Format_join___closed__1;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_9);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_9);
x_18 = l_Lean_Format_paren___closed__2;
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_9);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_9);
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_14);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_9);
x_23 = l_Lean_Format_paren___closed__2;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_9);
return x_24;
}
}
}
obj* l___private_init_lean_compiler_ir_format_7__formatParam(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_7__formatParam___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_paramHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_7__formatParam), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatAlt___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" →");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatAlt___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("default →");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_formatAlt___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_IR_formatAlt___main___closed__1;
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_10);
x_13 = lean::apply_1(x_1, x_5);
x_14 = lean::box(1);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_10);
x_16 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_10);
return x_17;
}
else
{
obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_3, 0);
lean::inc(x_18);
lean::dec(x_3);
x_19 = lean::apply_1(x_1, x_18);
x_20 = 0;
x_21 = lean::box(1);
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_20);
x_23 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_IR_formatAlt___main___closed__2;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_20);
return x_25;
}
}
}
obj* l_Lean_IR_formatAlt(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_formatAlt___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = l___private_init_lean_compiler_ir_format_7__formatParam___main(x_7);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_8);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_formatParams(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_formatParams___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_formatParams(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = 0;
x_10 = lean::box(1);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
lean::inc(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatFnBody___main), 2, 1);
lean::closure_set(x_12, 0, x_1);
lean::inc(x_1);
x_13 = l_Lean_IR_formatAlt___main(x_12, x_1, x_8);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_4, x_15);
lean::dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("let ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(";");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" :=");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("set ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("] := ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("setTag ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("uset ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__8() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("sset ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__9() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("] : ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__10() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("inc");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__11() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_string("inc");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string(" ");
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string("");
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = 0;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__12() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("dec");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__13() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_string("dec");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string(" ");
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string("");
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = 0;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__14() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("del ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__15() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("mdata ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__16() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("case ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__17() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" of");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__18() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("ret ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__19() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("jmp ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__20() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("⊥");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_formatFnBody___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_Nat_repr(x_3);
x_8 = l_Lean_IR_VarId_HasToString___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l_Lean_IR_formatFnBody___main___closed__1;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_11);
x_16 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_4);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_11);
x_18 = l_Lean_formatEntry___main___closed__1;
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_11);
x_20 = l___private_init_lean_compiler_ir_format_5__formatExpr___main(x_5);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_11);
x_22 = l_Lean_IR_formatFnBody___main___closed__2;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_11);
x_24 = lean::box(1);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_11);
x_26 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_11);
return x_27;
}
case 1:
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_2, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_2, 2);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_2, 3);
lean::inc(x_31);
lean::dec(x_2);
x_32 = l_Nat_repr(x_28);
x_33 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_34 = lean::string_append(x_33, x_32);
lean::dec(x_32);
x_35 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::box(0);
x_38 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_29, x_29, x_36, x_37);
lean::dec(x_29);
x_39 = 0;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_38);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_39);
x_41 = l_Lean_IR_formatFnBody___main___closed__3;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_39);
lean::inc(x_1);
x_43 = l_Lean_IR_formatFnBody___main(x_1, x_30);
x_44 = lean::box(1);
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_39);
lean::inc(x_1);
x_46 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_46, 0, x_1);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_42);
lean::cnstr_set(x_47, 1, x_46);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_39);
x_48 = l_Lean_IR_formatFnBody___main___closed__2;
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_39);
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_39);
x_51 = l_Lean_IR_formatFnBody___main(x_1, x_31);
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_39);
return x_52;
}
case 2:
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_53 = lean::cnstr_get(x_2, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_2, 1);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_2, 2);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_2, 3);
lean::inc(x_56);
lean::dec(x_2);
x_57 = l_Nat_repr(x_53);
x_58 = l_Lean_IR_VarId_HasToString___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_60 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = 0;
x_62 = l_Lean_IR_formatFnBody___main___closed__4;
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_60);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_61);
x_64 = l_Lean_Format_sbracket___closed__1;
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_61);
x_66 = l_Nat_repr(x_54);
x_67 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*2, x_61);
x_69 = l_Lean_IR_formatFnBody___main___closed__5;
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_61);
x_71 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_55);
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_61);
x_73 = l_Lean_IR_formatFnBody___main___closed__2;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_61);
x_75 = lean::box(1);
x_76 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*2, x_61);
x_77 = l_Lean_IR_formatFnBody___main(x_1, x_56);
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_61);
return x_78;
}
case 3:
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_79 = lean::cnstr_get(x_2, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_2, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_2, 2);
lean::inc(x_81);
lean::dec(x_2);
x_82 = l_Nat_repr(x_79);
x_83 = l_Lean_IR_VarId_HasToString___closed__1;
x_84 = lean::string_append(x_83, x_82);
lean::dec(x_82);
x_85 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = 0;
x_87 = l_Lean_IR_formatFnBody___main___closed__6;
x_88 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_85);
lean::cnstr_set_scalar(x_88, sizeof(void*)*2, x_86);
x_89 = l_Lean_formatEntry___main___closed__1;
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_89);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_86);
x_91 = l_Nat_repr(x_80);
x_92 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_93 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set(x_93, 1, x_92);
lean::cnstr_set_scalar(x_93, sizeof(void*)*2, x_86);
x_94 = l_Lean_IR_formatFnBody___main___closed__2;
x_95 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_94);
lean::cnstr_set_scalar(x_95, sizeof(void*)*2, x_86);
x_96 = lean::box(1);
x_97 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*2, x_86);
x_98 = l_Lean_IR_formatFnBody___main(x_1, x_81);
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_86);
return x_99;
}
case 4:
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_100 = lean::cnstr_get(x_2, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_2, 1);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_2, 2);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_2, 3);
lean::inc(x_103);
lean::dec(x_2);
x_104 = l_Nat_repr(x_100);
x_105 = l_Lean_IR_VarId_HasToString___closed__1;
x_106 = lean::string_append(x_105, x_104);
lean::dec(x_104);
x_107 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_107, 0, x_106);
x_108 = 0;
x_109 = l_Lean_IR_formatFnBody___main___closed__7;
x_110 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_107);
lean::cnstr_set_scalar(x_110, sizeof(void*)*2, x_108);
x_111 = l_Lean_Format_sbracket___closed__1;
x_112 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_111);
lean::cnstr_set_scalar(x_112, sizeof(void*)*2, x_108);
x_113 = l_Nat_repr(x_101);
x_114 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_114, 0, x_113);
x_115 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_114);
lean::cnstr_set_scalar(x_115, sizeof(void*)*2, x_108);
x_116 = l_Lean_IR_formatFnBody___main___closed__5;
x_117 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set(x_117, 1, x_116);
lean::cnstr_set_scalar(x_117, sizeof(void*)*2, x_108);
x_118 = l_Nat_repr(x_102);
x_119 = lean::string_append(x_105, x_118);
lean::dec(x_118);
x_120 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_120, 0, x_119);
x_121 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set(x_121, 1, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*2, x_108);
x_122 = l_Lean_IR_formatFnBody___main___closed__2;
x_123 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
lean::cnstr_set_scalar(x_123, sizeof(void*)*2, x_108);
x_124 = lean::box(1);
x_125 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_125, 0, x_123);
lean::cnstr_set(x_125, 1, x_124);
lean::cnstr_set_scalar(x_125, sizeof(void*)*2, x_108);
x_126 = l_Lean_IR_formatFnBody___main(x_1, x_103);
x_127 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_126);
lean::cnstr_set_scalar(x_127, sizeof(void*)*2, x_108);
return x_127;
}
case 5:
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_128 = lean::cnstr_get(x_2, 0);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_2, 1);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_2, 2);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_2, 3);
lean::inc(x_131);
x_132 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_133 = lean::cnstr_get(x_2, 4);
lean::inc(x_133);
lean::dec(x_2);
x_134 = l_Nat_repr(x_128);
x_135 = l_Lean_IR_VarId_HasToString___closed__1;
x_136 = lean::string_append(x_135, x_134);
lean::dec(x_134);
x_137 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_137, 0, x_136);
x_138 = 0;
x_139 = l_Lean_IR_formatFnBody___main___closed__8;
x_140 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_137);
lean::cnstr_set_scalar(x_140, sizeof(void*)*2, x_138);
x_141 = l_Lean_Format_sbracket___closed__1;
x_142 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_142, 0, x_140);
lean::cnstr_set(x_142, 1, x_141);
lean::cnstr_set_scalar(x_142, sizeof(void*)*2, x_138);
x_143 = l_Nat_repr(x_129);
x_144 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_144, 0, x_143);
x_145 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_145, 0, x_142);
lean::cnstr_set(x_145, 1, x_144);
lean::cnstr_set_scalar(x_145, sizeof(void*)*2, x_138);
x_146 = l_Lean_formatKVMap___closed__1;
x_147 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_146);
lean::cnstr_set_scalar(x_147, sizeof(void*)*2, x_138);
x_148 = l_Nat_repr(x_130);
x_149 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_149, 0, x_148);
x_150 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_150, 0, x_147);
lean::cnstr_set(x_150, 1, x_149);
lean::cnstr_set_scalar(x_150, sizeof(void*)*2, x_138);
x_151 = l_Lean_IR_formatFnBody___main___closed__9;
x_152 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_152, 0, x_150);
lean::cnstr_set(x_152, 1, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*2, x_138);
x_153 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_132);
x_154 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_153);
lean::cnstr_set_scalar(x_154, sizeof(void*)*2, x_138);
x_155 = l_Lean_formatEntry___main___closed__1;
x_156 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_156, 0, x_154);
lean::cnstr_set(x_156, 1, x_155);
lean::cnstr_set_scalar(x_156, sizeof(void*)*2, x_138);
x_157 = l_Nat_repr(x_131);
x_158 = lean::string_append(x_135, x_157);
lean::dec(x_157);
x_159 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_159, 0, x_158);
x_160 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_160, 0, x_156);
lean::cnstr_set(x_160, 1, x_159);
lean::cnstr_set_scalar(x_160, sizeof(void*)*2, x_138);
x_161 = l_Lean_IR_formatFnBody___main___closed__2;
x_162 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*2, x_138);
x_163 = lean::box(1);
x_164 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_164, 0, x_162);
lean::cnstr_set(x_164, 1, x_163);
lean::cnstr_set_scalar(x_164, sizeof(void*)*2, x_138);
x_165 = l_Lean_IR_formatFnBody___main(x_1, x_133);
x_166 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_166, 0, x_164);
lean::cnstr_set(x_166, 1, x_165);
lean::cnstr_set_scalar(x_166, sizeof(void*)*2, x_138);
return x_166;
}
case 6:
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; uint8 x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_167 = lean::cnstr_get(x_2, 0);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_2, 1);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_2, 2);
lean::inc(x_169);
lean::dec(x_2);
x_170 = lean::mk_nat_obj(1u);
x_171 = lean::nat_dec_eq(x_168, x_170);
x_172 = l_Nat_repr(x_167);
x_173 = l_Lean_IR_VarId_HasToString___closed__1;
x_174 = lean::string_append(x_173, x_172);
lean::dec(x_172);
x_175 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_175, 0, x_174);
x_176 = l_Lean_IR_formatFnBody___main(x_1, x_169);
if (x_171 == 0)
{
obj* x_177; obj* x_178; uint8 x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_177 = l_Nat_repr(x_168);
x_178 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_178, 0, x_177);
x_179 = 0;
x_180 = l_Lean_Format_sbracket___closed__1;
x_181 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_178);
lean::cnstr_set_scalar(x_181, sizeof(void*)*2, x_179);
x_182 = l_Lean_Format_sbracket___closed__2;
x_183 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_183, 0, x_181);
lean::cnstr_set(x_183, 1, x_182);
lean::cnstr_set_scalar(x_183, sizeof(void*)*2, x_179);
x_184 = l_Lean_Format_sbracket___closed__3;
x_185 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_185, 0, x_184);
lean::cnstr_set(x_185, 1, x_183);
x_186 = l_Lean_Format_group___main(x_185);
x_187 = l_Lean_IR_formatFnBody___main___closed__10;
x_188 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_186);
lean::cnstr_set_scalar(x_188, sizeof(void*)*2, x_179);
x_189 = l_Lean_Format_flatten___main___closed__1;
x_190 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_190, 0, x_188);
lean::cnstr_set(x_190, 1, x_189);
lean::cnstr_set_scalar(x_190, sizeof(void*)*2, x_179);
x_191 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_175);
lean::cnstr_set_scalar(x_191, sizeof(void*)*2, x_179);
x_192 = l_Lean_IR_formatFnBody___main___closed__2;
x_193 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_193, 0, x_191);
lean::cnstr_set(x_193, 1, x_192);
lean::cnstr_set_scalar(x_193, sizeof(void*)*2, x_179);
x_194 = lean::box(1);
x_195 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_195, 0, x_193);
lean::cnstr_set(x_195, 1, x_194);
lean::cnstr_set_scalar(x_195, sizeof(void*)*2, x_179);
x_196 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_196, 0, x_195);
lean::cnstr_set(x_196, 1, x_176);
lean::cnstr_set_scalar(x_196, sizeof(void*)*2, x_179);
return x_196;
}
else
{
uint8 x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
lean::dec(x_168);
x_197 = 0;
x_198 = l_Lean_IR_formatFnBody___main___closed__11;
x_199 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_199, 0, x_198);
lean::cnstr_set(x_199, 1, x_175);
lean::cnstr_set_scalar(x_199, sizeof(void*)*2, x_197);
x_200 = l_Lean_IR_formatFnBody___main___closed__2;
x_201 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_201, 0, x_199);
lean::cnstr_set(x_201, 1, x_200);
lean::cnstr_set_scalar(x_201, sizeof(void*)*2, x_197);
x_202 = lean::box(1);
x_203 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_203, 0, x_201);
lean::cnstr_set(x_203, 1, x_202);
lean::cnstr_set_scalar(x_203, sizeof(void*)*2, x_197);
x_204 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_176);
lean::cnstr_set_scalar(x_204, sizeof(void*)*2, x_197);
return x_204;
}
}
case 7:
{
obj* x_205; obj* x_206; obj* x_207; obj* x_208; uint8 x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
x_205 = lean::cnstr_get(x_2, 0);
lean::inc(x_205);
x_206 = lean::cnstr_get(x_2, 1);
lean::inc(x_206);
x_207 = lean::cnstr_get(x_2, 2);
lean::inc(x_207);
lean::dec(x_2);
x_208 = lean::mk_nat_obj(1u);
x_209 = lean::nat_dec_eq(x_206, x_208);
x_210 = l_Nat_repr(x_205);
x_211 = l_Lean_IR_VarId_HasToString___closed__1;
x_212 = lean::string_append(x_211, x_210);
lean::dec(x_210);
x_213 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_213, 0, x_212);
x_214 = l_Lean_IR_formatFnBody___main(x_1, x_207);
if (x_209 == 0)
{
obj* x_215; obj* x_216; uint8 x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
x_215 = l_Nat_repr(x_206);
x_216 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_216, 0, x_215);
x_217 = 0;
x_218 = l_Lean_Format_sbracket___closed__1;
x_219 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_219, 0, x_218);
lean::cnstr_set(x_219, 1, x_216);
lean::cnstr_set_scalar(x_219, sizeof(void*)*2, x_217);
x_220 = l_Lean_Format_sbracket___closed__2;
x_221 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_221, 0, x_219);
lean::cnstr_set(x_221, 1, x_220);
lean::cnstr_set_scalar(x_221, sizeof(void*)*2, x_217);
x_222 = l_Lean_Format_sbracket___closed__3;
x_223 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_223, 0, x_222);
lean::cnstr_set(x_223, 1, x_221);
x_224 = l_Lean_Format_group___main(x_223);
x_225 = l_Lean_IR_formatFnBody___main___closed__12;
x_226 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_224);
lean::cnstr_set_scalar(x_226, sizeof(void*)*2, x_217);
x_227 = l_Lean_Format_flatten___main___closed__1;
x_228 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_228, 0, x_226);
lean::cnstr_set(x_228, 1, x_227);
lean::cnstr_set_scalar(x_228, sizeof(void*)*2, x_217);
x_229 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_213);
lean::cnstr_set_scalar(x_229, sizeof(void*)*2, x_217);
x_230 = l_Lean_IR_formatFnBody___main___closed__2;
x_231 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_231, 0, x_229);
lean::cnstr_set(x_231, 1, x_230);
lean::cnstr_set_scalar(x_231, sizeof(void*)*2, x_217);
x_232 = lean::box(1);
x_233 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_233, 0, x_231);
lean::cnstr_set(x_233, 1, x_232);
lean::cnstr_set_scalar(x_233, sizeof(void*)*2, x_217);
x_234 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_214);
lean::cnstr_set_scalar(x_234, sizeof(void*)*2, x_217);
return x_234;
}
else
{
uint8 x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_206);
x_235 = 0;
x_236 = l_Lean_IR_formatFnBody___main___closed__13;
x_237 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_237, 0, x_236);
lean::cnstr_set(x_237, 1, x_213);
lean::cnstr_set_scalar(x_237, sizeof(void*)*2, x_235);
x_238 = l_Lean_IR_formatFnBody___main___closed__2;
x_239 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_239, 0, x_237);
lean::cnstr_set(x_239, 1, x_238);
lean::cnstr_set_scalar(x_239, sizeof(void*)*2, x_235);
x_240 = lean::box(1);
x_241 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_241, 0, x_239);
lean::cnstr_set(x_241, 1, x_240);
lean::cnstr_set_scalar(x_241, sizeof(void*)*2, x_235);
x_242 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_214);
lean::cnstr_set_scalar(x_242, sizeof(void*)*2, x_235);
return x_242;
}
}
case 8:
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; uint8 x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
x_243 = lean::cnstr_get(x_2, 0);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_2, 1);
lean::inc(x_244);
lean::dec(x_2);
x_245 = l_Nat_repr(x_243);
x_246 = l_Lean_IR_VarId_HasToString___closed__1;
x_247 = lean::string_append(x_246, x_245);
lean::dec(x_245);
x_248 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_248, 0, x_247);
x_249 = 0;
x_250 = l_Lean_IR_formatFnBody___main___closed__14;
x_251 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_248);
lean::cnstr_set_scalar(x_251, sizeof(void*)*2, x_249);
x_252 = l_Lean_IR_formatFnBody___main___closed__2;
x_253 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_253, 0, x_251);
lean::cnstr_set(x_253, 1, x_252);
lean::cnstr_set_scalar(x_253, sizeof(void*)*2, x_249);
x_254 = lean::box(1);
x_255 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_255, 0, x_253);
lean::cnstr_set(x_255, 1, x_254);
lean::cnstr_set_scalar(x_255, sizeof(void*)*2, x_249);
x_256 = l_Lean_IR_formatFnBody___main(x_1, x_244);
x_257 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_257, 0, x_255);
lean::cnstr_set(x_257, 1, x_256);
lean::cnstr_set_scalar(x_257, sizeof(void*)*2, x_249);
return x_257;
}
case 9:
{
obj* x_258; obj* x_259; obj* x_260; uint8 x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
x_258 = lean::cnstr_get(x_2, 0);
lean::inc(x_258);
x_259 = lean::cnstr_get(x_2, 1);
lean::inc(x_259);
lean::dec(x_2);
x_260 = l_Lean_formatKVMap(x_258);
x_261 = 0;
x_262 = l_Lean_IR_formatFnBody___main___closed__15;
x_263 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_260);
lean::cnstr_set_scalar(x_263, sizeof(void*)*2, x_261);
x_264 = l_Lean_IR_formatFnBody___main___closed__2;
x_265 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_265, 0, x_263);
lean::cnstr_set(x_265, 1, x_264);
lean::cnstr_set_scalar(x_265, sizeof(void*)*2, x_261);
x_266 = lean::box(1);
x_267 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_267, 0, x_265);
lean::cnstr_set(x_267, 1, x_266);
lean::cnstr_set_scalar(x_267, sizeof(void*)*2, x_261);
x_268 = l_Lean_IR_formatFnBody___main(x_1, x_259);
x_269 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_269, 0, x_267);
lean::cnstr_set(x_269, 1, x_268);
lean::cnstr_set_scalar(x_269, sizeof(void*)*2, x_261);
return x_269;
}
case 10:
{
obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; uint8 x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_270 = lean::cnstr_get(x_2, 1);
lean::inc(x_270);
x_271 = lean::cnstr_get(x_2, 2);
lean::inc(x_271);
lean::dec(x_2);
x_272 = l_Nat_repr(x_270);
x_273 = l_Lean_IR_VarId_HasToString___closed__1;
x_274 = lean::string_append(x_273, x_272);
lean::dec(x_272);
x_275 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_275, 0, x_274);
x_276 = 0;
x_277 = l_Lean_IR_formatFnBody___main___closed__16;
x_278 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_275);
lean::cnstr_set_scalar(x_278, sizeof(void*)*2, x_276);
x_279 = l_Lean_IR_formatFnBody___main___closed__17;
x_280 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_280, 0, x_278);
lean::cnstr_set(x_280, 1, x_279);
lean::cnstr_set_scalar(x_280, sizeof(void*)*2, x_276);
x_281 = lean::mk_nat_obj(0u);
x_282 = lean::box(0);
x_283 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_271, x_271, x_281, x_282);
lean::dec(x_271);
x_284 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_284, 0, x_280);
lean::cnstr_set(x_284, 1, x_283);
lean::cnstr_set_scalar(x_284, sizeof(void*)*2, x_276);
return x_284;
}
case 11:
{
obj* x_285; obj* x_286; uint8 x_287; obj* x_288; obj* x_289; 
lean::dec(x_1);
x_285 = lean::cnstr_get(x_2, 0);
lean::inc(x_285);
lean::dec(x_2);
x_286 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_285);
x_287 = 0;
x_288 = l_Lean_IR_formatFnBody___main___closed__18;
x_289 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_289, 0, x_288);
lean::cnstr_set(x_289, 1, x_286);
lean::cnstr_set_scalar(x_289, sizeof(void*)*2, x_287);
return x_289;
}
case 12:
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; uint8 x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_1);
x_290 = lean::cnstr_get(x_2, 0);
lean::inc(x_290);
x_291 = lean::cnstr_get(x_2, 1);
lean::inc(x_291);
lean::dec(x_2);
x_292 = l_Nat_repr(x_290);
x_293 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_294 = lean::string_append(x_293, x_292);
lean::dec(x_292);
x_295 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_295, 0, x_294);
x_296 = 0;
x_297 = l_Lean_IR_formatFnBody___main___closed__19;
x_298 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_295);
lean::cnstr_set_scalar(x_298, sizeof(void*)*2, x_296);
x_299 = lean::mk_nat_obj(0u);
x_300 = lean::box(0);
x_301 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_291, x_291, x_299, x_300);
lean::dec(x_291);
x_302 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_302, 0, x_298);
lean::cnstr_set(x_302, 1, x_301);
lean::cnstr_set_scalar(x_302, sizeof(void*)*2, x_296);
return x_302;
}
default: 
{
obj* x_303; 
lean::dec(x_1);
x_303 = l_Lean_IR_formatFnBody___main___closed__20;
return x_303;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_IR_formatFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_formatFnBody___main(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_fnBodyHasFormat() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(2u);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatFnBody), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_fnBodyHasToString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(2u);
x_3 = l_Lean_IR_formatFnBody___main(x_2, x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_IR_formatDecl___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("def ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_formatDecl___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("extern ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_IR_formatDecl___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_3);
x_9 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_IR_formatDecl___main___closed__1;
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_10);
x_13 = lean::mk_nat_obj(0u);
x_14 = lean::box(0);
x_15 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_13, x_14);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_10);
x_17 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_10);
x_19 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_5);
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_10);
x_21 = l_Lean_IR_formatFnBody___main___closed__3;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_10);
lean::inc(x_1);
x_23 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_24 = lean::box(1);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_10);
x_26 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_22);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_10);
return x_27;
}
else
{
obj* x_28; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_1);
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_2, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
lean::dec(x_2);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_28);
x_33 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = 0;
x_35 = l_Lean_IR_formatDecl___main___closed__2;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_33);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_34);
x_37 = lean::mk_nat_obj(0u);
x_38 = lean::box(0);
x_39 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_29, x_29, x_37, x_38);
lean::dec(x_29);
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_34);
x_41 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_34);
x_43 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_30);
x_44 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set_scalar(x_44, sizeof(void*)*2, x_34);
return x_44;
}
}
}
obj* l_Lean_IR_formatDecl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_formatDecl___main(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_declHasFormat() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(2u);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatDecl), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
namespace lean {
namespace ir {
obj* decl_to_string_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(2u);
x_3 = l_Lean_IR_formatDecl___main(x_2, x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
}
}
obj* _init_l_Lean_IR_declHasToString() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(lean::ir::decl_to_string_core), 1, 0);
return x_1;
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_format(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_format(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1 = _init_l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1);
l_Lean_IR_argHasFormat = _init_l_Lean_IR_argHasFormat();
lean::mark_persistent(l_Lean_IR_argHasFormat);
l_Lean_IR_litValHasFormat = _init_l_Lean_IR_litValHasFormat();
lean::mark_persistent(l_Lean_IR_litValHasFormat);
l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1 = _init_l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1);
l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2 = _init_l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2);
l_Lean_IR_ctorInfoHasFormat = _init_l_Lean_IR_ctorInfoHasFormat();
lean::mark_persistent(l_Lean_IR_ctorInfoHasFormat);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13);
l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14 = _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14);
l_Lean_IR_exprHasFormat = _init_l_Lean_IR_exprHasFormat();
lean::mark_persistent(l_Lean_IR_exprHasFormat);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7);
l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8 = _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8);
l_Lean_IR_typeHasFormat = _init_l_Lean_IR_typeHasFormat();
lean::mark_persistent(l_Lean_IR_typeHasFormat);
l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1 = _init_l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1);
l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2 = _init_l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2);
l_Lean_IR_paramHasFormat = _init_l_Lean_IR_paramHasFormat();
lean::mark_persistent(l_Lean_IR_paramHasFormat);
l_Lean_IR_formatAlt___main___closed__1 = _init_l_Lean_IR_formatAlt___main___closed__1();
lean::mark_persistent(l_Lean_IR_formatAlt___main___closed__1);
l_Lean_IR_formatAlt___main___closed__2 = _init_l_Lean_IR_formatAlt___main___closed__2();
lean::mark_persistent(l_Lean_IR_formatAlt___main___closed__2);
l_Lean_IR_formatFnBody___main___closed__1 = _init_l_Lean_IR_formatFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__1);
l_Lean_IR_formatFnBody___main___closed__2 = _init_l_Lean_IR_formatFnBody___main___closed__2();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__2);
l_Lean_IR_formatFnBody___main___closed__3 = _init_l_Lean_IR_formatFnBody___main___closed__3();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__3);
l_Lean_IR_formatFnBody___main___closed__4 = _init_l_Lean_IR_formatFnBody___main___closed__4();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__4);
l_Lean_IR_formatFnBody___main___closed__5 = _init_l_Lean_IR_formatFnBody___main___closed__5();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__5);
l_Lean_IR_formatFnBody___main___closed__6 = _init_l_Lean_IR_formatFnBody___main___closed__6();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__6);
l_Lean_IR_formatFnBody___main___closed__7 = _init_l_Lean_IR_formatFnBody___main___closed__7();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__7);
l_Lean_IR_formatFnBody___main___closed__8 = _init_l_Lean_IR_formatFnBody___main___closed__8();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__8);
l_Lean_IR_formatFnBody___main___closed__9 = _init_l_Lean_IR_formatFnBody___main___closed__9();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__9);
l_Lean_IR_formatFnBody___main___closed__10 = _init_l_Lean_IR_formatFnBody___main___closed__10();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__10);
l_Lean_IR_formatFnBody___main___closed__11 = _init_l_Lean_IR_formatFnBody___main___closed__11();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__11);
l_Lean_IR_formatFnBody___main___closed__12 = _init_l_Lean_IR_formatFnBody___main___closed__12();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__12);
l_Lean_IR_formatFnBody___main___closed__13 = _init_l_Lean_IR_formatFnBody___main___closed__13();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__13);
l_Lean_IR_formatFnBody___main___closed__14 = _init_l_Lean_IR_formatFnBody___main___closed__14();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__14);
l_Lean_IR_formatFnBody___main___closed__15 = _init_l_Lean_IR_formatFnBody___main___closed__15();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__15);
l_Lean_IR_formatFnBody___main___closed__16 = _init_l_Lean_IR_formatFnBody___main___closed__16();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__16);
l_Lean_IR_formatFnBody___main___closed__17 = _init_l_Lean_IR_formatFnBody___main___closed__17();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__17);
l_Lean_IR_formatFnBody___main___closed__18 = _init_l_Lean_IR_formatFnBody___main___closed__18();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__18);
l_Lean_IR_formatFnBody___main___closed__19 = _init_l_Lean_IR_formatFnBody___main___closed__19();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__19);
l_Lean_IR_formatFnBody___main___closed__20 = _init_l_Lean_IR_formatFnBody___main___closed__20();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__20);
l_Lean_IR_fnBodyHasFormat = _init_l_Lean_IR_fnBodyHasFormat();
lean::mark_persistent(l_Lean_IR_fnBodyHasFormat);
l_Lean_IR_formatDecl___main___closed__1 = _init_l_Lean_IR_formatDecl___main___closed__1();
lean::mark_persistent(l_Lean_IR_formatDecl___main___closed__1);
l_Lean_IR_formatDecl___main___closed__2 = _init_l_Lean_IR_formatDecl___main___closed__2();
lean::mark_persistent(l_Lean_IR_formatDecl___main___closed__2);
l_Lean_IR_declHasFormat = _init_l_Lean_IR_declHasFormat();
lean::mark_persistent(l_Lean_IR_declHasFormat);
l_Lean_IR_declHasToString = _init_l_Lean_IR_declHasToString();
lean::mark_persistent(l_Lean_IR_declHasToString);
return w;
}
