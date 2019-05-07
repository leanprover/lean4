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
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main(uint8);
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___boxed(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__6;
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1;
namespace lean {
namespace ir {
obj* decl_to_string_core(obj*);
}}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__17;
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_IR_formatAlt___main___closed__1;
extern obj* l_Lean_Options_empty;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__13;
obj* l_Lean_IR_declHasFormat;
extern obj* l_Lean_Format_join___closed__1;
obj* l___private_init_lean_compiler_ir_format_1__formatArg(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2___boxed(obj*, obj*, obj*, obj*);
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
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(obj*, obj*, obj*, obj*);
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
obj* l_Lean_IR_formatFnBody___main___closed__3;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal___main(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__9;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2;
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
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1___boxed(obj*);
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2;
obj* l_Lean_IR_declHasToString;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType(uint8);
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5;
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11;
obj* l_Lean_IR_formatFnBody___main___closed__10;
obj* l_Lean_IR_formatFnBody___main___closed__5;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody(obj*, obj*);
obj* l_Lean_IR_ctorInfoHasFormat;
extern obj* l_Lean_formatKVMap___closed__1;
obj* l_Lean_IR_formatDecl___main___closed__2;
obj* l_Lean_IR_formatFnBody___main___closed__16;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7;
obj* l___private_init_lean_compiler_ir_format_2__formatArray(obj*);
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo(obj*);
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(obj*);
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
obj* l_Lean_IR_exprHasFormat;
obj* l_Lean_IR_formatFnBody___main___closed__18;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj*);
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg(obj*, obj*);
obj* l_Lean_IR_litValHasFormat;
obj* l_Lean_IR_fnBodyHasToString(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
obj* l_Lean_IR_formatAlt___main___closed__2;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___boxed(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1(obj*);
obj* l_String_quote(obj*);
obj* l_Lean_IR_paramHasFormat;
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatFnBody___main___spec__1(obj*);
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14;
obj* l_Lean_IR_formatFnBody___main___closed__7;
obj* l_Lean_IR_formatFnBody___main___closed__4;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7;
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6;
obj* l_Lean_IR_formatFnBody___main(obj*, obj*);
obj* _init_l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x97\xbe");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_1__formatArg___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Nat_repr(x_1);
x_5 = l_Lean_IR_VarId_HasToString___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_6);
return x_8;
}
else
{
obj* x_9; 
x_9 = l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1;
return x_9;
}
}
}
obj* l___private_init_lean_compiler_ir_format_1__formatArg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_argHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_1__formatArg), 1, 0);
return x_0;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::array_fget(x_2, x_3);
x_11 = 0;
x_12 = l_Lean_Format_flatten___main___closed__1;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = x_13;
lean::inc(x_0);
x_16 = lean::apply_1(x_0, x_10);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_11);
x_18 = x_17;
x_19 = lean::mk_nat_obj(1ul);
x_20 = lean::nat_add(x_3, x_19);
lean::dec(x_3);
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(x_0, x_1, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_2__formatArray___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_2__formatArray___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_2__formatArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Nat_repr(x_1);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_String_quote(x_6);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l___private_init_lean_compiler_ir_format_3__formatLitVal(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_3__formatLitVal___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_litValHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_3__formatLitVal), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("ctor_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(".");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; uint8 x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 4);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_Nat_repr(x_3);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = 0;
x_13 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__1;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = lean::mk_nat_obj(0ul);
x_17 = lean::nat_dec_lt(x_16, x_5);
x_18 = lean::box(0);
x_19 = lean_name_dec_eq(x_1, x_18);
if (x_17 == 0)
{
uint8 x_20; 
x_20 = lean::nat_dec_lt(x_16, x_7);
if (x_20 == 0)
{
lean::dec(x_7);
lean::dec(x_5);
if (x_19 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_23 = l_Lean_Format_sbracket___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_12);
x_25 = x_24;
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_12);
x_30 = x_29;
x_31 = l_Lean_Format_sbracket___closed__2;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_12);
x_33 = x_32;
return x_33;
}
else
{
lean::dec(x_1);
return x_15;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_35 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_15);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_12);
x_37 = x_36;
x_38 = l_Nat_repr(x_5);
x_39 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_37);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_12);
x_41 = x_40;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_12);
x_43 = x_42;
x_44 = l_Nat_repr(x_7);
x_45 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*2, x_12);
x_47 = x_46;
if (x_19 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_48 = l_Lean_Format_sbracket___closed__1;
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_12);
x_50 = x_49;
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_1);
x_53 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_12);
x_55 = x_54;
x_56 = l_Lean_Format_sbracket___closed__2;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_12);
x_58 = x_57;
return x_58;
}
else
{
lean::dec(x_1);
return x_47;
}
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_60 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main___closed__2;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_15);
lean::cnstr_set(x_61, 1, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_12);
x_62 = x_61;
x_63 = l_Nat_repr(x_5);
x_64 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_12);
x_66 = x_65;
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_60);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_12);
x_68 = x_67;
x_69 = l_Nat_repr(x_7);
x_70 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_12);
x_72 = x_71;
if (x_19 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_73 = l_Lean_Format_sbracket___closed__1;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_12);
x_75 = x_74;
x_76 = l_Lean_Name_toString___closed__1;
x_77 = l_Lean_Name_toStringWithSep___main(x_76, x_1);
x_78 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_12);
x_80 = x_79;
x_81 = l_Lean_Format_sbracket___closed__2;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_12);
x_83 = x_82;
return x_83;
}
else
{
lean::dec(x_1);
return x_72;
}
}
}
}
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_ctorInfoHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_4__formatCtorInfo), 1, 0);
return x_0;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = 0;
x_10 = l_Lean_Format_flatten___main___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_8);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_2 = x_17;
x_3 = x_15;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::box(0);
x_3 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_0, x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("reset ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("reuse");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::mk_string(" ");
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = lean::mk_string("");
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = 0;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_6);
x_8 = x_7;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_6);
x_10 = x_9;
return x_10;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" in ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("reuse");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::mk_string(" ");
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = lean::mk_string("!");
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = 0;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_6);
x_8 = x_7;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_6);
x_10 = x_9;
return x_10;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("proj_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("uproj_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("sproj_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("pap ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("app ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("box ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unbox ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("isShared ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("isTaggedPtr ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_11; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_1);
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::box(0);
x_9 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_3, x_3, x_7, x_8);
lean::dec(x_3);
x_11 = 0;
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_11);
x_13 = x_12;
return x_13;
}
case 1:
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = l_Nat_repr(x_14);
x_18 = l_Lean_IR_VarId_HasToString___closed__1;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = 0;
x_23 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_21);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_22);
x_25 = x_24;
return x_25;
}
case 2:
{
obj* x_26; obj* x_28; uint8 x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_31 = lean::cnstr_get(x_0, 2);
lean::inc(x_31);
lean::dec(x_0);
x_34 = l_Nat_repr(x_26);
x_35 = l_Lean_IR_VarId_HasToString___closed__1;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_38 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_38, 0, x_36);
x_39 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_28);
x_40 = lean::mk_nat_obj(0ul);
x_41 = lean::box(0);
x_42 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_31, x_31, x_40, x_41);
lean::dec(x_31);
if (x_30 == 0)
{
uint8 x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_44 = 0;
x_45 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_46 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_38);
lean::cnstr_set_scalar(x_46, sizeof(void*)*2, x_44);
x_47 = x_46;
x_48 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3;
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_44);
x_50 = x_49;
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_39);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_44);
x_52 = x_51;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_42);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_44);
x_54 = x_53;
return x_54;
}
else
{
uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_55 = 0;
x_56 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_38);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_55);
x_58 = x_57;
x_59 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3;
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_55);
x_61 = x_60;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_39);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_55);
x_63 = x_62;
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_42);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_55);
x_65 = x_64;
return x_65;
}
}
case 3:
{
obj* x_66; obj* x_68; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_0, 1);
lean::inc(x_68);
lean::dec(x_0);
x_71 = l_Nat_repr(x_66);
x_72 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = 0;
x_74 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5;
x_75 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_72);
lean::cnstr_set_scalar(x_75, sizeof(void*)*2, x_73);
x_76 = x_75;
x_77 = l_Lean_Format_flatten___main___closed__1;
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_73);
x_79 = x_78;
x_80 = l_Nat_repr(x_68);
x_81 = l_Lean_IR_VarId_HasToString___closed__1;
x_82 = lean::string_append(x_81, x_80);
lean::dec(x_80);
x_84 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_84, 0, x_82);
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_79);
lean::cnstr_set(x_85, 1, x_84);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_73);
x_86 = x_85;
return x_86;
}
case 4:
{
obj* x_87; obj* x_89; obj* x_92; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_105; obj* x_106; obj* x_107; 
x_87 = lean::cnstr_get(x_0, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_0, 1);
lean::inc(x_89);
lean::dec(x_0);
x_92 = l_Nat_repr(x_87);
x_93 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_94 = 0;
x_95 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6;
x_96 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_93);
lean::cnstr_set_scalar(x_96, sizeof(void*)*2, x_94);
x_97 = x_96;
x_98 = l_Lean_Format_flatten___main___closed__1;
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_94);
x_100 = x_99;
x_101 = l_Nat_repr(x_89);
x_102 = l_Lean_IR_VarId_HasToString___closed__1;
x_103 = lean::string_append(x_102, x_101);
lean::dec(x_101);
x_105 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_105, 0, x_103);
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_100);
lean::cnstr_set(x_106, 1, x_105);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_94);
x_107 = x_106;
return x_107;
}
case 5:
{
obj* x_108; obj* x_110; obj* x_112; obj* x_115; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_135; obj* x_136; obj* x_137; 
x_108 = lean::cnstr_get(x_0, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_0, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_0, 2);
lean::inc(x_112);
lean::dec(x_0);
x_115 = l_Nat_repr(x_108);
x_116 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_116, 0, x_115);
x_117 = 0;
x_118 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7;
x_119 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set_scalar(x_119, sizeof(void*)*2, x_117);
x_120 = x_119;
x_121 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8;
x_122 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_121);
lean::cnstr_set_scalar(x_122, sizeof(void*)*2, x_117);
x_123 = x_122;
x_124 = l_Nat_repr(x_110);
x_125 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_125, 0, x_124);
x_126 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_125);
lean::cnstr_set_scalar(x_126, sizeof(void*)*2, x_117);
x_127 = x_126;
x_128 = l_Lean_Format_flatten___main___closed__1;
x_129 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_128);
lean::cnstr_set_scalar(x_129, sizeof(void*)*2, x_117);
x_130 = x_129;
x_131 = l_Nat_repr(x_112);
x_132 = l_Lean_IR_VarId_HasToString___closed__1;
x_133 = lean::string_append(x_132, x_131);
lean::dec(x_131);
x_135 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_135, 0, x_133);
x_136 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_136, 0, x_130);
lean::cnstr_set(x_136, 1, x_135);
lean::cnstr_set_scalar(x_136, sizeof(void*)*2, x_117);
x_137 = x_136;
return x_137;
}
case 6:
{
obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; uint8 x_150; obj* x_151; obj* x_152; 
x_138 = lean::cnstr_get(x_0, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_0, 1);
lean::inc(x_140);
lean::dec(x_0);
x_143 = l_Lean_Name_toString___closed__1;
x_144 = l_Lean_Name_toStringWithSep___main(x_143, x_138);
x_145 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
x_146 = lean::mk_nat_obj(0ul);
x_147 = lean::box(0);
x_148 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_140, x_140, x_146, x_147);
lean::dec(x_140);
x_150 = 0;
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_145);
lean::cnstr_set(x_151, 1, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_150);
x_152 = x_151;
return x_152;
}
case 7:
{
obj* x_153; obj* x_155; obj* x_158; obj* x_159; obj* x_160; uint8 x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_169; obj* x_170; 
x_153 = lean::cnstr_get(x_0, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_0, 1);
lean::inc(x_155);
lean::dec(x_0);
x_158 = l_Lean_Name_toString___closed__1;
x_159 = l_Lean_Name_toStringWithSep___main(x_158, x_153);
x_160 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_160, 0, x_159);
x_161 = 0;
x_162 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9;
x_163 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_160);
lean::cnstr_set_scalar(x_163, sizeof(void*)*2, x_161);
x_164 = x_163;
x_165 = lean::mk_nat_obj(0ul);
x_166 = lean::box(0);
x_167 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_155, x_155, x_165, x_166);
lean::dec(x_155);
x_169 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_169, 0, x_164);
lean::cnstr_set(x_169, 1, x_167);
lean::cnstr_set_scalar(x_169, sizeof(void*)*2, x_161);
x_170 = x_169;
return x_170;
}
case 8:
{
obj* x_171; obj* x_173; obj* x_176; obj* x_177; obj* x_178; obj* x_180; uint8 x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_189; obj* x_190; 
x_171 = lean::cnstr_get(x_0, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_0, 1);
lean::inc(x_173);
lean::dec(x_0);
x_176 = l_Nat_repr(x_171);
x_177 = l_Lean_IR_VarId_HasToString___closed__1;
x_178 = lean::string_append(x_177, x_176);
lean::dec(x_176);
x_180 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_180, 0, x_178);
x_181 = 0;
x_182 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10;
x_183 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_183, 0, x_182);
lean::cnstr_set(x_183, 1, x_180);
lean::cnstr_set_scalar(x_183, sizeof(void*)*2, x_181);
x_184 = x_183;
x_185 = lean::mk_nat_obj(0ul);
x_186 = lean::box(0);
x_187 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_173, x_173, x_185, x_186);
lean::dec(x_173);
x_189 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_189, 0, x_184);
lean::cnstr_set(x_189, 1, x_187);
lean::cnstr_set_scalar(x_189, sizeof(void*)*2, x_181);
x_190 = x_189;
return x_190;
}
case 9:
{
obj* x_191; obj* x_194; obj* x_195; obj* x_196; obj* x_198; uint8 x_199; obj* x_200; obj* x_201; obj* x_202; 
x_191 = lean::cnstr_get(x_0, 0);
lean::inc(x_191);
lean::dec(x_0);
x_194 = l_Nat_repr(x_191);
x_195 = l_Lean_IR_VarId_HasToString___closed__1;
x_196 = lean::string_append(x_195, x_194);
lean::dec(x_194);
x_198 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_198, 0, x_196);
x_199 = 0;
x_200 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11;
x_201 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_201, 0, x_200);
lean::cnstr_set(x_201, 1, x_198);
lean::cnstr_set_scalar(x_201, sizeof(void*)*2, x_199);
x_202 = x_201;
return x_202;
}
case 10:
{
obj* x_203; obj* x_206; obj* x_207; obj* x_208; obj* x_210; uint8 x_211; obj* x_212; obj* x_213; obj* x_214; 
x_203 = lean::cnstr_get(x_0, 0);
lean::inc(x_203);
lean::dec(x_0);
x_206 = l_Nat_repr(x_203);
x_207 = l_Lean_IR_VarId_HasToString___closed__1;
x_208 = lean::string_append(x_207, x_206);
lean::dec(x_206);
x_210 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_210, 0, x_208);
x_211 = 0;
x_212 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12;
x_213 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_213, 0, x_212);
lean::cnstr_set(x_213, 1, x_210);
lean::cnstr_set_scalar(x_213, sizeof(void*)*2, x_211);
x_214 = x_213;
return x_214;
}
case 11:
{
obj* x_215; obj* x_218; 
x_215 = lean::cnstr_get(x_0, 0);
lean::inc(x_215);
lean::dec(x_0);
x_218 = l___private_init_lean_compiler_ir_format_3__formatLitVal___main(x_215);
return x_218;
}
case 12:
{
obj* x_219; obj* x_222; obj* x_223; obj* x_224; obj* x_226; uint8 x_227; obj* x_228; obj* x_229; obj* x_230; 
x_219 = lean::cnstr_get(x_0, 0);
lean::inc(x_219);
lean::dec(x_0);
x_222 = l_Nat_repr(x_219);
x_223 = l_Lean_IR_VarId_HasToString___closed__1;
x_224 = lean::string_append(x_223, x_222);
lean::dec(x_222);
x_226 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_226, 0, x_224);
x_227 = 0;
x_228 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13;
x_229 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_226);
lean::cnstr_set_scalar(x_229, sizeof(void*)*2, x_227);
x_230 = x_229;
return x_230;
}
default:
{
obj* x_231; obj* x_234; obj* x_235; obj* x_236; obj* x_238; uint8 x_239; obj* x_240; obj* x_241; obj* x_242; 
x_231 = lean::cnstr_get(x_0, 0);
lean::inc(x_231);
lean::dec(x_0);
x_234 = l_Nat_repr(x_231);
x_235 = l_Lean_IR_VarId_HasToString___closed__1;
x_236 = lean::string_append(x_235, x_234);
lean::dec(x_234);
x_238 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_238, 0, x_236);
x_239 = 0;
x_240 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14;
x_241 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_241, 0, x_240);
lean::cnstr_set(x_241, 1, x_238);
lean::cnstr_set_scalar(x_241, sizeof(void*)*2, x_239);
x_242 = x_241;
return x_242;
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_5__formatExpr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_5__formatExpr___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_exprHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_5__formatExpr), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("float");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u8");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u16");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u32");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u64");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("usize");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("obj");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("tobj");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__2;
return x_2;
}
case 2:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__3;
return x_3;
}
case 3:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__4;
return x_4;
}
case 4:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__5;
return x_5;
}
case 5:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__6;
return x_6;
}
case 6:
{
obj* x_7; 
x_7 = l___private_init_lean_compiler_ir_format_1__formatArg___main___closed__1;
return x_7;
}
case 7:
{
obj* x_8; 
x_8 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__7;
return x_8;
}
default:
{
obj* x_9; 
x_9 = l___private_init_lean_compiler_ir_format_6__formatIRType___main___closed__8;
return x_9;
}
}
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_6__formatIRType___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l___private_init_lean_compiler_ir_format_6__formatIRType(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_typeHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_6__formatIRType___boxed), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" : ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("@^ ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_format_7__formatParam___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_3; uint8 x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_4 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1 + 1);
lean::dec(x_0);
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_8);
x_11 = 0;
x_12 = l_Lean_Format_paren___closed__1;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = x_13;
x_15 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_11);
x_17 = x_16;
x_18 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_4);
if (x_3 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = l_Lean_Format_join___closed__1;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_11);
x_21 = x_20;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_11);
x_23 = x_22;
x_24 = l_Lean_Format_paren___closed__2;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_11);
x_26 = x_25;
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_27 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__2;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_17);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_11);
x_29 = x_28;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_18);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_11);
x_31 = x_30;
x_32 = l_Lean_Format_paren___closed__2;
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_11);
x_34 = x_33;
return x_34;
}
}
}
obj* l___private_init_lean_compiler_ir_format_7__formatParam(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_7__formatParam___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_paramHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_format_7__formatParam), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_IR_formatAlt___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" \xe2\x86\x92");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatAlt___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("default \xe2\x86\x92");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_formatAlt___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_8);
x_13 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = 0;
x_15 = l_Lean_IR_formatAlt___main___closed__1;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_14);
x_17 = x_16;
x_18 = lean::apply_1(x_0, x_5);
x_19 = lean::box(1);
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_14);
x_21 = x_20;
x_22 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_14);
x_24 = x_23;
return x_24;
}
else
{
obj* x_25; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_28 = lean::apply_1(x_0, x_25);
x_29 = 0;
x_30 = lean::box(1);
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_29);
x_32 = x_31;
x_33 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_32);
x_34 = l_Lean_IR_formatAlt___main___closed__2;
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_29);
x_36 = x_35;
return x_36;
}
}
}
obj* l_Lean_IR_formatAlt(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_formatAlt___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = 0;
x_10 = l_Lean_Format_flatten___main___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l___private_init_lean_compiler_ir_format_7__formatParam___main(x_8);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_2 = x_17;
x_3 = x_15;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatFnBody___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::box(0);
x_3 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_0, x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_10 = lean::array_fget(x_2, x_3);
x_11 = 0;
x_12 = lean::box(1);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = x_13;
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatFnBody___main), 2, 1);
lean::closure_set(x_16, 0, x_0);
lean::inc(x_0);
x_18 = l_Lean_IR_formatAlt___main(x_16, x_0, x_10);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_11);
x_20 = x_19;
x_21 = lean::mk_nat_obj(1ul);
x_22 = lean::nat_add(x_3, x_21);
lean::dec(x_3);
x_3 = x_22;
x_4 = x_20;
goto _start;
}
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("let ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(";");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" :=");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("set ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("] := ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("uset ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("sset ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("] : ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("release ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("];");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("inc ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("dec ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("mdata ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("case ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__15() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" of");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__16() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("ret ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__17() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("jmp ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__18() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x8a\xa5");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_formatFnBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; uint8 x_4; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Nat_repr(x_2);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_14, 0, x_12);
x_15 = 0;
x_16 = l_Lean_IR_formatFnBody___main___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
x_18 = x_17;
x_19 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_15);
x_21 = x_20;
x_22 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_4);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_15);
x_24 = x_23;
x_25 = l_Lean_formatEntry___main___closed__1;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_15);
x_27 = x_26;
x_28 = l___private_init_lean_compiler_ir_format_5__formatExpr___main(x_5);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_15);
x_30 = x_29;
x_31 = l_Lean_IR_formatFnBody___main___closed__2;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_15);
x_33 = x_32;
x_34 = lean::box(1);
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_15);
x_36 = x_35;
x_37 = l_Lean_IR_formatFnBody___main(x_0, x_7);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_15);
x_39 = x_38;
return x_39;
}
case 1:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::dec(x_1);
x_49 = l_Nat_repr(x_40);
x_50 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_51 = lean::string_append(x_50, x_49);
lean::dec(x_49);
x_53 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_53, 0, x_51);
x_54 = lean::mk_nat_obj(0ul);
x_55 = lean::box(0);
x_56 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_42, x_42, x_54, x_55);
lean::dec(x_42);
x_58 = 0;
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_53);
lean::cnstr_set(x_59, 1, x_56);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_58);
x_60 = x_59;
x_61 = l_Lean_IR_formatFnBody___main___closed__3;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_58);
x_63 = x_62;
lean::inc(x_0);
x_65 = l_Lean_IR_formatFnBody___main(x_0, x_44);
x_66 = lean::box(1);
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_58);
x_68 = x_67;
lean::inc(x_0);
x_70 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_70, 0, x_0);
lean::cnstr_set(x_70, 1, x_68);
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_63);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_58);
x_72 = x_71;
x_73 = l_Lean_IR_formatFnBody___main___closed__2;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_58);
x_75 = x_74;
x_76 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_66);
lean::cnstr_set_scalar(x_76, sizeof(void*)*2, x_58);
x_77 = x_76;
x_78 = l_Lean_IR_formatFnBody___main(x_0, x_46);
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_58);
x_80 = x_79;
return x_80;
}
case 2:
{
obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_94; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_81 = lean::cnstr_get(x_1, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_1, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_1, 2);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_1, 3);
lean::inc(x_87);
lean::dec(x_1);
x_90 = l_Nat_repr(x_81);
x_91 = l_Lean_IR_VarId_HasToString___closed__1;
x_92 = lean::string_append(x_91, x_90);
lean::dec(x_90);
x_94 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_94, 0, x_92);
x_95 = 0;
x_96 = l_Lean_IR_formatFnBody___main___closed__4;
x_97 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_94);
lean::cnstr_set_scalar(x_97, sizeof(void*)*2, x_95);
x_98 = x_97;
x_99 = l_Lean_Format_sbracket___closed__1;
x_100 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set(x_100, 1, x_99);
lean::cnstr_set_scalar(x_100, sizeof(void*)*2, x_95);
x_101 = x_100;
x_102 = l_Nat_repr(x_83);
x_103 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_101);
lean::cnstr_set(x_104, 1, x_103);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_95);
x_105 = x_104;
x_106 = l_Lean_IR_formatFnBody___main___closed__5;
x_107 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_106);
lean::cnstr_set_scalar(x_107, sizeof(void*)*2, x_95);
x_108 = x_107;
x_109 = l_Nat_repr(x_85);
x_110 = lean::string_append(x_91, x_109);
lean::dec(x_109);
x_112 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_112, 0, x_110);
x_113 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_113, 0, x_108);
lean::cnstr_set(x_113, 1, x_112);
lean::cnstr_set_scalar(x_113, sizeof(void*)*2, x_95);
x_114 = x_113;
x_115 = l_Lean_IR_formatFnBody___main___closed__2;
x_116 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_116, 0, x_114);
lean::cnstr_set(x_116, 1, x_115);
lean::cnstr_set_scalar(x_116, sizeof(void*)*2, x_95);
x_117 = x_116;
x_118 = lean::box(1);
x_119 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set(x_119, 1, x_118);
lean::cnstr_set_scalar(x_119, sizeof(void*)*2, x_95);
x_120 = x_119;
x_121 = l_Lean_IR_formatFnBody___main(x_0, x_87);
x_122 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_121);
lean::cnstr_set_scalar(x_122, sizeof(void*)*2, x_95);
x_123 = x_122;
return x_123;
}
case 3:
{
obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_133; obj* x_134; obj* x_135; obj* x_137; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_124 = lean::cnstr_get(x_1, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_1, 1);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_1, 2);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_1, 3);
lean::inc(x_130);
lean::dec(x_1);
x_133 = l_Nat_repr(x_124);
x_134 = l_Lean_IR_VarId_HasToString___closed__1;
x_135 = lean::string_append(x_134, x_133);
lean::dec(x_133);
x_137 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_137, 0, x_135);
x_138 = 0;
x_139 = l_Lean_IR_formatFnBody___main___closed__6;
x_140 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_137);
lean::cnstr_set_scalar(x_140, sizeof(void*)*2, x_138);
x_141 = x_140;
x_142 = l_Lean_Format_sbracket___closed__1;
x_143 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_143, 0, x_141);
lean::cnstr_set(x_143, 1, x_142);
lean::cnstr_set_scalar(x_143, sizeof(void*)*2, x_138);
x_144 = x_143;
x_145 = l_Nat_repr(x_126);
x_146 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_146, 0, x_145);
x_147 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_147, 0, x_144);
lean::cnstr_set(x_147, 1, x_146);
lean::cnstr_set_scalar(x_147, sizeof(void*)*2, x_138);
x_148 = x_147;
x_149 = l_Lean_IR_formatFnBody___main___closed__5;
x_150 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_150, 0, x_148);
lean::cnstr_set(x_150, 1, x_149);
lean::cnstr_set_scalar(x_150, sizeof(void*)*2, x_138);
x_151 = x_150;
x_152 = l_Nat_repr(x_128);
x_153 = lean::string_append(x_134, x_152);
lean::dec(x_152);
x_155 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_155, 0, x_153);
x_156 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_156, 0, x_151);
lean::cnstr_set(x_156, 1, x_155);
lean::cnstr_set_scalar(x_156, sizeof(void*)*2, x_138);
x_157 = x_156;
x_158 = l_Lean_IR_formatFnBody___main___closed__2;
x_159 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_159, 0, x_157);
lean::cnstr_set(x_159, 1, x_158);
lean::cnstr_set_scalar(x_159, sizeof(void*)*2, x_138);
x_160 = x_159;
x_161 = lean::box(1);
x_162 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*2, x_138);
x_163 = x_162;
x_164 = l_Lean_IR_formatFnBody___main(x_0, x_130);
x_165 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_165, 0, x_163);
lean::cnstr_set(x_165, 1, x_164);
lean::cnstr_set_scalar(x_165, sizeof(void*)*2, x_138);
x_166 = x_165;
return x_166;
}
case 4:
{
obj* x_167; obj* x_169; obj* x_171; obj* x_173; uint8 x_175; obj* x_176; obj* x_179; obj* x_180; obj* x_181; obj* x_183; uint8 x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_167 = lean::cnstr_get(x_1, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_1, 1);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_1, 2);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_1, 3);
lean::inc(x_173);
x_175 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_176 = lean::cnstr_get(x_1, 4);
lean::inc(x_176);
lean::dec(x_1);
x_179 = l_Nat_repr(x_167);
x_180 = l_Lean_IR_VarId_HasToString___closed__1;
x_181 = lean::string_append(x_180, x_179);
lean::dec(x_179);
x_183 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_183, 0, x_181);
x_184 = 0;
x_185 = l_Lean_IR_formatFnBody___main___closed__7;
x_186 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_183);
lean::cnstr_set_scalar(x_186, sizeof(void*)*2, x_184);
x_187 = x_186;
x_188 = l_Lean_Format_sbracket___closed__1;
x_189 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_188);
lean::cnstr_set_scalar(x_189, sizeof(void*)*2, x_184);
x_190 = x_189;
x_191 = l_Nat_repr(x_169);
x_192 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_192, 0, x_191);
x_193 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_193, 0, x_190);
lean::cnstr_set(x_193, 1, x_192);
lean::cnstr_set_scalar(x_193, sizeof(void*)*2, x_184);
x_194 = x_193;
x_195 = l_Lean_formatKVMap___closed__1;
x_196 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_195);
lean::cnstr_set_scalar(x_196, sizeof(void*)*2, x_184);
x_197 = x_196;
x_198 = l_Nat_repr(x_171);
x_199 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_199, 0, x_198);
x_200 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_200, 0, x_197);
lean::cnstr_set(x_200, 1, x_199);
lean::cnstr_set_scalar(x_200, sizeof(void*)*2, x_184);
x_201 = x_200;
x_202 = l_Lean_IR_formatFnBody___main___closed__8;
x_203 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_203, 0, x_201);
lean::cnstr_set(x_203, 1, x_202);
lean::cnstr_set_scalar(x_203, sizeof(void*)*2, x_184);
x_204 = x_203;
x_205 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_175);
x_206 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_206, 0, x_204);
lean::cnstr_set(x_206, 1, x_205);
lean::cnstr_set_scalar(x_206, sizeof(void*)*2, x_184);
x_207 = x_206;
x_208 = l_Lean_formatEntry___main___closed__1;
x_209 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_209, 0, x_207);
lean::cnstr_set(x_209, 1, x_208);
lean::cnstr_set_scalar(x_209, sizeof(void*)*2, x_184);
x_210 = x_209;
x_211 = l_Nat_repr(x_173);
x_212 = lean::string_append(x_180, x_211);
lean::dec(x_211);
x_214 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_214, 0, x_212);
x_215 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_215, 0, x_210);
lean::cnstr_set(x_215, 1, x_214);
lean::cnstr_set_scalar(x_215, sizeof(void*)*2, x_184);
x_216 = x_215;
x_217 = l_Lean_IR_formatFnBody___main___closed__2;
x_218 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_218, 0, x_216);
lean::cnstr_set(x_218, 1, x_217);
lean::cnstr_set_scalar(x_218, sizeof(void*)*2, x_184);
x_219 = x_218;
x_220 = lean::box(1);
x_221 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_221, 0, x_219);
lean::cnstr_set(x_221, 1, x_220);
lean::cnstr_set_scalar(x_221, sizeof(void*)*2, x_184);
x_222 = x_221;
x_223 = l_Lean_IR_formatFnBody___main(x_0, x_176);
x_224 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_224, 0, x_222);
lean::cnstr_set(x_224, 1, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*2, x_184);
x_225 = x_224;
return x_225;
}
case 5:
{
obj* x_226; obj* x_228; obj* x_230; obj* x_233; obj* x_234; obj* x_235; obj* x_237; uint8 x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
x_226 = lean::cnstr_get(x_1, 0);
lean::inc(x_226);
x_228 = lean::cnstr_get(x_1, 1);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_1, 2);
lean::inc(x_230);
lean::dec(x_1);
x_233 = l_Nat_repr(x_226);
x_234 = l_Lean_IR_VarId_HasToString___closed__1;
x_235 = lean::string_append(x_234, x_233);
lean::dec(x_233);
x_237 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_237, 0, x_235);
x_238 = 0;
x_239 = l_Lean_IR_formatFnBody___main___closed__9;
x_240 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_237);
lean::cnstr_set_scalar(x_240, sizeof(void*)*2, x_238);
x_241 = x_240;
x_242 = l_Lean_Format_sbracket___closed__1;
x_243 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_243, 0, x_241);
lean::cnstr_set(x_243, 1, x_242);
lean::cnstr_set_scalar(x_243, sizeof(void*)*2, x_238);
x_244 = x_243;
x_245 = l_Nat_repr(x_228);
x_246 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_246, 0, x_245);
x_247 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_247, 0, x_244);
lean::cnstr_set(x_247, 1, x_246);
lean::cnstr_set_scalar(x_247, sizeof(void*)*2, x_238);
x_248 = x_247;
x_249 = l_Lean_IR_formatFnBody___main___closed__10;
x_250 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_250, 0, x_248);
lean::cnstr_set(x_250, 1, x_249);
lean::cnstr_set_scalar(x_250, sizeof(void*)*2, x_238);
x_251 = x_250;
x_252 = lean::box(1);
x_253 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_253, 0, x_251);
lean::cnstr_set(x_253, 1, x_252);
lean::cnstr_set_scalar(x_253, sizeof(void*)*2, x_238);
x_254 = x_253;
x_255 = l_Lean_IR_formatFnBody___main(x_0, x_230);
x_256 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_256, 0, x_254);
lean::cnstr_set(x_256, 1, x_255);
lean::cnstr_set_scalar(x_256, sizeof(void*)*2, x_238);
x_257 = x_256;
return x_257;
}
case 6:
{
obj* x_258; obj* x_260; obj* x_262; obj* x_265; obj* x_266; obj* x_267; obj* x_269; uint8 x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; uint8 x_275; obj* x_276; 
x_258 = lean::cnstr_get(x_1, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_1, 1);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_1, 2);
lean::inc(x_262);
lean::dec(x_1);
x_265 = l_Nat_repr(x_258);
x_266 = l_Lean_IR_VarId_HasToString___closed__1;
x_267 = lean::string_append(x_266, x_265);
lean::dec(x_265);
x_269 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_269, 0, x_267);
x_270 = 0;
x_271 = l_Lean_IR_formatFnBody___main___closed__11;
x_272 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_269);
lean::cnstr_set_scalar(x_272, sizeof(void*)*2, x_270);
x_273 = x_272;
x_274 = lean::mk_nat_obj(1ul);
x_275 = lean::nat_dec_eq(x_260, x_274);
x_276 = l_Lean_IR_formatFnBody___main(x_0, x_262);
if (x_275 == 0)
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; 
x_277 = l_Nat_repr(x_260);
x_278 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_278, 0, x_277);
x_279 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_279, 0, x_273);
lean::cnstr_set(x_279, 1, x_278);
lean::cnstr_set_scalar(x_279, sizeof(void*)*2, x_270);
x_280 = x_279;
x_281 = l_Lean_IR_formatFnBody___main___closed__2;
x_282 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_282, 0, x_280);
lean::cnstr_set(x_282, 1, x_281);
lean::cnstr_set_scalar(x_282, sizeof(void*)*2, x_270);
x_283 = x_282;
x_284 = lean::box(1);
x_285 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_285, 0, x_283);
lean::cnstr_set(x_285, 1, x_284);
lean::cnstr_set_scalar(x_285, sizeof(void*)*2, x_270);
x_286 = x_285;
x_287 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_276);
lean::cnstr_set_scalar(x_287, sizeof(void*)*2, x_270);
x_288 = x_287;
return x_288;
}
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
lean::dec(x_260);
x_290 = l_Lean_Format_join___closed__1;
x_291 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_291, 0, x_273);
lean::cnstr_set(x_291, 1, x_290);
lean::cnstr_set_scalar(x_291, sizeof(void*)*2, x_270);
x_292 = x_291;
x_293 = l_Lean_IR_formatFnBody___main___closed__2;
x_294 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_294, 0, x_292);
lean::cnstr_set(x_294, 1, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*2, x_270);
x_295 = x_294;
x_296 = lean::box(1);
x_297 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_297, 0, x_295);
lean::cnstr_set(x_297, 1, x_296);
lean::cnstr_set_scalar(x_297, sizeof(void*)*2, x_270);
x_298 = x_297;
x_299 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_299, 0, x_298);
lean::cnstr_set(x_299, 1, x_276);
lean::cnstr_set_scalar(x_299, sizeof(void*)*2, x_270);
x_300 = x_299;
return x_300;
}
}
case 7:
{
obj* x_301; obj* x_303; obj* x_305; obj* x_308; obj* x_309; obj* x_310; obj* x_312; uint8 x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; uint8 x_318; obj* x_319; 
x_301 = lean::cnstr_get(x_1, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_1, 1);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_1, 2);
lean::inc(x_305);
lean::dec(x_1);
x_308 = l_Nat_repr(x_301);
x_309 = l_Lean_IR_VarId_HasToString___closed__1;
x_310 = lean::string_append(x_309, x_308);
lean::dec(x_308);
x_312 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_312, 0, x_310);
x_313 = 0;
x_314 = l_Lean_IR_formatFnBody___main___closed__12;
x_315 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_312);
lean::cnstr_set_scalar(x_315, sizeof(void*)*2, x_313);
x_316 = x_315;
x_317 = lean::mk_nat_obj(1ul);
x_318 = lean::nat_dec_eq(x_303, x_317);
x_319 = l_Lean_IR_formatFnBody___main(x_0, x_305);
if (x_318 == 0)
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; 
x_320 = l_Nat_repr(x_303);
x_321 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_321, 0, x_320);
x_322 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_322, 0, x_316);
lean::cnstr_set(x_322, 1, x_321);
lean::cnstr_set_scalar(x_322, sizeof(void*)*2, x_313);
x_323 = x_322;
x_324 = l_Lean_IR_formatFnBody___main___closed__2;
x_325 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_325, 0, x_323);
lean::cnstr_set(x_325, 1, x_324);
lean::cnstr_set_scalar(x_325, sizeof(void*)*2, x_313);
x_326 = x_325;
x_327 = lean::box(1);
x_328 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_328, 0, x_326);
lean::cnstr_set(x_328, 1, x_327);
lean::cnstr_set_scalar(x_328, sizeof(void*)*2, x_313);
x_329 = x_328;
x_330 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_330, 0, x_329);
lean::cnstr_set(x_330, 1, x_319);
lean::cnstr_set_scalar(x_330, sizeof(void*)*2, x_313);
x_331 = x_330;
return x_331;
}
else
{
obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_303);
x_333 = l_Lean_Format_join___closed__1;
x_334 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_334, 0, x_316);
lean::cnstr_set(x_334, 1, x_333);
lean::cnstr_set_scalar(x_334, sizeof(void*)*2, x_313);
x_335 = x_334;
x_336 = l_Lean_IR_formatFnBody___main___closed__2;
x_337 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_337, 0, x_335);
lean::cnstr_set(x_337, 1, x_336);
lean::cnstr_set_scalar(x_337, sizeof(void*)*2, x_313);
x_338 = x_337;
x_339 = lean::box(1);
x_340 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_340, 0, x_338);
lean::cnstr_set(x_340, 1, x_339);
lean::cnstr_set_scalar(x_340, sizeof(void*)*2, x_313);
x_341 = x_340;
x_342 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_342, 0, x_341);
lean::cnstr_set(x_342, 1, x_319);
lean::cnstr_set_scalar(x_342, sizeof(void*)*2, x_313);
x_343 = x_342;
return x_343;
}
}
case 8:
{
obj* x_344; obj* x_346; obj* x_349; uint8 x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; 
x_344 = lean::cnstr_get(x_1, 0);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_1, 1);
lean::inc(x_346);
lean::dec(x_1);
x_349 = l_Lean_formatKVMap(x_344);
x_350 = 0;
x_351 = l_Lean_IR_formatFnBody___main___closed__13;
x_352 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_352, 0, x_351);
lean::cnstr_set(x_352, 1, x_349);
lean::cnstr_set_scalar(x_352, sizeof(void*)*2, x_350);
x_353 = x_352;
x_354 = l_Lean_IR_formatFnBody___main___closed__2;
x_355 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_355, 0, x_353);
lean::cnstr_set(x_355, 1, x_354);
lean::cnstr_set_scalar(x_355, sizeof(void*)*2, x_350);
x_356 = x_355;
x_357 = lean::box(1);
x_358 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_358, 0, x_356);
lean::cnstr_set(x_358, 1, x_357);
lean::cnstr_set_scalar(x_358, sizeof(void*)*2, x_350);
x_359 = x_358;
x_360 = l_Lean_IR_formatFnBody___main(x_0, x_346);
x_361 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_361, 0, x_359);
lean::cnstr_set(x_361, 1, x_360);
lean::cnstr_set_scalar(x_361, sizeof(void*)*2, x_350);
x_362 = x_361;
return x_362;
}
case 9:
{
obj* x_363; obj* x_365; obj* x_368; obj* x_369; obj* x_370; obj* x_372; uint8 x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_384; obj* x_385; 
x_363 = lean::cnstr_get(x_1, 1);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_1, 2);
lean::inc(x_365);
lean::dec(x_1);
x_368 = l_Nat_repr(x_363);
x_369 = l_Lean_IR_VarId_HasToString___closed__1;
x_370 = lean::string_append(x_369, x_368);
lean::dec(x_368);
x_372 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_372, 0, x_370);
x_373 = 0;
x_374 = l_Lean_IR_formatFnBody___main___closed__14;
x_375 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_375, 0, x_374);
lean::cnstr_set(x_375, 1, x_372);
lean::cnstr_set_scalar(x_375, sizeof(void*)*2, x_373);
x_376 = x_375;
x_377 = l_Lean_IR_formatFnBody___main___closed__15;
x_378 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_378, 0, x_376);
lean::cnstr_set(x_378, 1, x_377);
lean::cnstr_set_scalar(x_378, sizeof(void*)*2, x_373);
x_379 = x_378;
x_380 = lean::mk_nat_obj(0ul);
x_381 = lean::box(0);
x_382 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(x_0, x_365, x_365, x_380, x_381);
lean::dec(x_365);
x_384 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_384, 0, x_379);
lean::cnstr_set(x_384, 1, x_382);
lean::cnstr_set_scalar(x_384, sizeof(void*)*2, x_373);
x_385 = x_384;
return x_385;
}
case 10:
{
obj* x_387; obj* x_390; uint8 x_391; obj* x_392; obj* x_393; obj* x_394; 
lean::dec(x_0);
x_387 = lean::cnstr_get(x_1, 0);
lean::inc(x_387);
lean::dec(x_1);
x_390 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_387);
x_391 = 0;
x_392 = l_Lean_IR_formatFnBody___main___closed__16;
x_393 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_393, 0, x_392);
lean::cnstr_set(x_393, 1, x_390);
lean::cnstr_set_scalar(x_393, sizeof(void*)*2, x_391);
x_394 = x_393;
return x_394;
}
case 11:
{
obj* x_396; obj* x_398; obj* x_401; obj* x_402; obj* x_403; obj* x_405; uint8 x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_414; obj* x_415; 
lean::dec(x_0);
x_396 = lean::cnstr_get(x_1, 0);
lean::inc(x_396);
x_398 = lean::cnstr_get(x_1, 1);
lean::inc(x_398);
lean::dec(x_1);
x_401 = l_Nat_repr(x_396);
x_402 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_403 = lean::string_append(x_402, x_401);
lean::dec(x_401);
x_405 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_405, 0, x_403);
x_406 = 0;
x_407 = l_Lean_IR_formatFnBody___main___closed__17;
x_408 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_408, 0, x_407);
lean::cnstr_set(x_408, 1, x_405);
lean::cnstr_set_scalar(x_408, sizeof(void*)*2, x_406);
x_409 = x_408;
x_410 = lean::mk_nat_obj(0ul);
x_411 = lean::box(0);
x_412 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_398, x_398, x_410, x_411);
lean::dec(x_398);
x_414 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_414, 0, x_409);
lean::cnstr_set(x_414, 1, x_412);
lean::cnstr_set_scalar(x_414, sizeof(void*)*2, x_406);
x_415 = x_414;
return x_415;
}
default:
{
obj* x_417; 
lean::dec(x_0);
x_417 = l_Lean_IR_formatFnBody___main___closed__18;
return x_417;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatFnBody___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_formatFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_formatFnBody___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_fnBodyHasFormat() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(2ul);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatFnBody), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_fnBodyHasToString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(2ul);
x_2 = l_Lean_IR_formatFnBody___main(x_1, x_0);
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Format_pretty(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_formatDecl___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("def ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatDecl___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("extern ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_formatDecl___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; uint8 x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_2);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = 0;
x_14 = l_Lean_IR_formatDecl___main___closed__1;
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_13);
x_16 = x_15;
x_17 = lean::mk_nat_obj(0ul);
x_18 = lean::box(0);
x_19 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_4, x_4, x_17, x_18);
lean::dec(x_4);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_13);
x_22 = x_21;
x_23 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_13);
x_25 = x_24;
x_26 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_6);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_13);
x_28 = x_27;
x_29 = l_Lean_IR_formatFnBody___main___closed__3;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_13);
x_31 = x_30;
lean::inc(x_0);
x_33 = l_Lean_IR_formatFnBody___main(x_0, x_7);
x_34 = lean::box(1);
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_13);
x_36 = x_35;
x_37 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_37, 0, x_0);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_31);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_13);
x_39 = x_38;
return x_39;
}
else
{
obj* x_41; obj* x_43; uint8 x_45; obj* x_47; obj* x_48; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_0);
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
lean::dec(x_1);
x_47 = l_Lean_Name_toString___closed__1;
x_48 = l_Lean_Name_toStringWithSep___main(x_47, x_41);
x_49 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = 0;
x_51 = l_Lean_IR_formatDecl___main___closed__2;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_49);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_50);
x_53 = x_52;
x_54 = lean::mk_nat_obj(0ul);
x_55 = lean::box(0);
x_56 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_43, x_43, x_54, x_55);
lean::dec(x_43);
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_56);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_50);
x_59 = x_58;
x_60 = l___private_init_lean_compiler_ir_format_7__formatParam___main___closed__1;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_50);
x_62 = x_61;
x_63 = l___private_init_lean_compiler_ir_format_6__formatIRType___main(x_45);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_50);
x_65 = x_64;
return x_65;
}
}
}
obj* l_Lean_IR_formatDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_formatDecl___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_declHasFormat() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(2ul);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatDecl), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
namespace lean {
namespace ir {
obj* decl_to_string_core(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(2ul);
x_2 = l_Lean_IR_formatDecl___main(x_1, x_0);
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Format_pretty(x_2, x_3);
return x_4;
}
}
}}
obj* _init_l_Lean_IR_declHasToString() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::ir::decl_to_string_core), 1, 0);
return x_0;
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
