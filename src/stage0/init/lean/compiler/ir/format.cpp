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
}}
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
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_2__formatArray___spec__1___boxed(obj*);
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
obj* l_Lean_IR_formatFnBody___main___closed__21;
obj* l___private_init_lean_compiler_ir_format_2__formatArray(obj*);
obj* l___private_init_lean_compiler_ir_format_4__formatCtorInfo(obj*);
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__1(obj*);
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
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
obj* l___private_init_lean_compiler_ir_format_2__formatArray___boxed(obj*);
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
x_0 = lean::mk_string("reset[");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("] ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3() {
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
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" in ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5() {
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
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("proj[");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("uproj[");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("sproj[");
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
obj* x_14; obj* x_16; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Nat_repr(x_14);
x_20 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = 0;
x_22 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__1;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_21);
x_24 = x_23;
x_25 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_21);
x_27 = x_26;
x_28 = l_Nat_repr(x_16);
x_29 = l_Lean_IR_VarId_HasToString___closed__1;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_32, 0, x_30);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_27);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_21);
x_34 = x_33;
return x_34;
}
case 2:
{
obj* x_35; obj* x_37; uint8 x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_40 = lean::cnstr_get(x_0, 2);
lean::inc(x_40);
lean::dec(x_0);
x_43 = l_Nat_repr(x_35);
x_44 = l_Lean_IR_VarId_HasToString___closed__1;
x_45 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_47 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_47, 0, x_45);
x_48 = l___private_init_lean_compiler_ir_format_4__formatCtorInfo___main(x_37);
x_49 = lean::mk_nat_obj(0ul);
x_50 = lean::box(0);
x_51 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_40, x_40, x_49, x_50);
lean::dec(x_40);
if (x_39 == 0)
{
uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_53 = 0;
x_54 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__3;
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_47);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_53);
x_56 = x_55;
x_57 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_53);
x_59 = x_58;
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_48);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_53);
x_61 = x_60;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_51);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_53);
x_63 = x_62;
return x_63;
}
else
{
uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_64 = 0;
x_65 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__5;
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_47);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_64);
x_67 = x_66;
x_68 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__4;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_64);
x_70 = x_69;
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_48);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_64);
x_72 = x_71;
x_73 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_51);
lean::cnstr_set_scalar(x_73, sizeof(void*)*2, x_64);
x_74 = x_73;
return x_74;
}
}
case 3:
{
obj* x_75; obj* x_77; obj* x_80; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_93; obj* x_94; obj* x_95; 
x_75 = lean::cnstr_get(x_0, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_0, 1);
lean::inc(x_77);
lean::dec(x_0);
x_80 = l_Nat_repr(x_75);
x_81 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = 0;
x_83 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__6;
x_84 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set_scalar(x_84, sizeof(void*)*2, x_82);
x_85 = x_84;
x_86 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_87 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*2, x_82);
x_88 = x_87;
x_89 = l_Nat_repr(x_77);
x_90 = l_Lean_IR_VarId_HasToString___closed__1;
x_91 = lean::string_append(x_90, x_89);
lean::dec(x_89);
x_93 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_93, 0, x_91);
x_94 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_94, 0, x_88);
lean::cnstr_set(x_94, 1, x_93);
lean::cnstr_set_scalar(x_94, sizeof(void*)*2, x_82);
x_95 = x_94;
return x_95;
}
case 4:
{
obj* x_96; obj* x_98; obj* x_101; obj* x_102; uint8 x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_114; obj* x_115; obj* x_116; 
x_96 = lean::cnstr_get(x_0, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_0, 1);
lean::inc(x_98);
lean::dec(x_0);
x_101 = l_Nat_repr(x_96);
x_102 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
x_103 = 0;
x_104 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__7;
x_105 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_102);
lean::cnstr_set_scalar(x_105, sizeof(void*)*2, x_103);
x_106 = x_105;
x_107 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_108 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_107);
lean::cnstr_set_scalar(x_108, sizeof(void*)*2, x_103);
x_109 = x_108;
x_110 = l_Nat_repr(x_98);
x_111 = l_Lean_IR_VarId_HasToString___closed__1;
x_112 = lean::string_append(x_111, x_110);
lean::dec(x_110);
x_114 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_114, 0, x_112);
x_115 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_115, 0, x_109);
lean::cnstr_set(x_115, 1, x_114);
lean::cnstr_set_scalar(x_115, sizeof(void*)*2, x_103);
x_116 = x_115;
return x_116;
}
case 5:
{
obj* x_117; obj* x_119; obj* x_121; obj* x_124; obj* x_125; uint8 x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_144; obj* x_145; obj* x_146; 
x_117 = lean::cnstr_get(x_0, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_0, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_0, 2);
lean::inc(x_121);
lean::dec(x_0);
x_124 = l_Nat_repr(x_117);
x_125 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_125, 0, x_124);
x_126 = 0;
x_127 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__8;
x_128 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_125);
lean::cnstr_set_scalar(x_128, sizeof(void*)*2, x_126);
x_129 = x_128;
x_130 = l_Lean_formatKVMap___closed__1;
x_131 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_131, 0, x_129);
lean::cnstr_set(x_131, 1, x_130);
lean::cnstr_set_scalar(x_131, sizeof(void*)*2, x_126);
x_132 = x_131;
x_133 = l_Nat_repr(x_119);
x_134 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_134, 0, x_133);
x_135 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_135, 0, x_132);
lean::cnstr_set(x_135, 1, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*2, x_126);
x_136 = x_135;
x_137 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__2;
x_138 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_138, 0, x_136);
lean::cnstr_set(x_138, 1, x_137);
lean::cnstr_set_scalar(x_138, sizeof(void*)*2, x_126);
x_139 = x_138;
x_140 = l_Nat_repr(x_121);
x_141 = l_Lean_IR_VarId_HasToString___closed__1;
x_142 = lean::string_append(x_141, x_140);
lean::dec(x_140);
x_144 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_144, 0, x_142);
x_145 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_145, 0, x_139);
lean::cnstr_set(x_145, 1, x_144);
lean::cnstr_set_scalar(x_145, sizeof(void*)*2, x_126);
x_146 = x_145;
return x_146;
}
case 6:
{
obj* x_147; obj* x_149; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; uint8 x_159; obj* x_160; obj* x_161; 
x_147 = lean::cnstr_get(x_0, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_0, 1);
lean::inc(x_149);
lean::dec(x_0);
x_152 = l_Lean_Name_toString___closed__1;
x_153 = l_Lean_Name_toStringWithSep___main(x_152, x_147);
x_154 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_154, 0, x_153);
x_155 = lean::mk_nat_obj(0ul);
x_156 = lean::box(0);
x_157 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_149, x_149, x_155, x_156);
lean::dec(x_149);
x_159 = 0;
x_160 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_160, 0, x_154);
lean::cnstr_set(x_160, 1, x_157);
lean::cnstr_set_scalar(x_160, sizeof(void*)*2, x_159);
x_161 = x_160;
return x_161;
}
case 7:
{
obj* x_162; obj* x_164; obj* x_167; obj* x_168; obj* x_169; uint8 x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_178; obj* x_179; 
x_162 = lean::cnstr_get(x_0, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_0, 1);
lean::inc(x_164);
lean::dec(x_0);
x_167 = l_Lean_Name_toString___closed__1;
x_168 = l_Lean_Name_toStringWithSep___main(x_167, x_162);
x_169 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_169, 0, x_168);
x_170 = 0;
x_171 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__9;
x_172 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_172, 0, x_171);
lean::cnstr_set(x_172, 1, x_169);
lean::cnstr_set_scalar(x_172, sizeof(void*)*2, x_170);
x_173 = x_172;
x_174 = lean::mk_nat_obj(0ul);
x_175 = lean::box(0);
x_176 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_164, x_164, x_174, x_175);
lean::dec(x_164);
x_178 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_178, 0, x_173);
lean::cnstr_set(x_178, 1, x_176);
lean::cnstr_set_scalar(x_178, sizeof(void*)*2, x_170);
x_179 = x_178;
return x_179;
}
case 8:
{
obj* x_180; obj* x_182; obj* x_185; obj* x_186; obj* x_187; obj* x_189; uint8 x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_198; obj* x_199; 
x_180 = lean::cnstr_get(x_0, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_0, 1);
lean::inc(x_182);
lean::dec(x_0);
x_185 = l_Nat_repr(x_180);
x_186 = l_Lean_IR_VarId_HasToString___closed__1;
x_187 = lean::string_append(x_186, x_185);
lean::dec(x_185);
x_189 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_189, 0, x_187);
x_190 = 0;
x_191 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__10;
x_192 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_189);
lean::cnstr_set_scalar(x_192, sizeof(void*)*2, x_190);
x_193 = x_192;
x_194 = lean::mk_nat_obj(0ul);
x_195 = lean::box(0);
x_196 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_182, x_182, x_194, x_195);
lean::dec(x_182);
x_198 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_198, 0, x_193);
lean::cnstr_set(x_198, 1, x_196);
lean::cnstr_set_scalar(x_198, sizeof(void*)*2, x_190);
x_199 = x_198;
return x_199;
}
case 9:
{
obj* x_200; obj* x_203; obj* x_204; obj* x_205; obj* x_207; uint8 x_208; obj* x_209; obj* x_210; obj* x_211; 
x_200 = lean::cnstr_get(x_0, 0);
lean::inc(x_200);
lean::dec(x_0);
x_203 = l_Nat_repr(x_200);
x_204 = l_Lean_IR_VarId_HasToString___closed__1;
x_205 = lean::string_append(x_204, x_203);
lean::dec(x_203);
x_207 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_207, 0, x_205);
x_208 = 0;
x_209 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__11;
x_210 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_207);
lean::cnstr_set_scalar(x_210, sizeof(void*)*2, x_208);
x_211 = x_210;
return x_211;
}
case 10:
{
obj* x_212; obj* x_215; obj* x_216; obj* x_217; obj* x_219; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; 
x_212 = lean::cnstr_get(x_0, 0);
lean::inc(x_212);
lean::dec(x_0);
x_215 = l_Nat_repr(x_212);
x_216 = l_Lean_IR_VarId_HasToString___closed__1;
x_217 = lean::string_append(x_216, x_215);
lean::dec(x_215);
x_219 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_219, 0, x_217);
x_220 = 0;
x_221 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__12;
x_222 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_222, 0, x_221);
lean::cnstr_set(x_222, 1, x_219);
lean::cnstr_set_scalar(x_222, sizeof(void*)*2, x_220);
x_223 = x_222;
return x_223;
}
case 11:
{
obj* x_224; obj* x_227; 
x_224 = lean::cnstr_get(x_0, 0);
lean::inc(x_224);
lean::dec(x_0);
x_227 = l___private_init_lean_compiler_ir_format_3__formatLitVal___main(x_224);
return x_227;
}
case 12:
{
obj* x_228; obj* x_231; obj* x_232; obj* x_233; obj* x_235; uint8 x_236; obj* x_237; obj* x_238; obj* x_239; 
x_228 = lean::cnstr_get(x_0, 0);
lean::inc(x_228);
lean::dec(x_0);
x_231 = l_Nat_repr(x_228);
x_232 = l_Lean_IR_VarId_HasToString___closed__1;
x_233 = lean::string_append(x_232, x_231);
lean::dec(x_231);
x_235 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_235, 0, x_233);
x_236 = 0;
x_237 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__13;
x_238 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_238, 0, x_237);
lean::cnstr_set(x_238, 1, x_235);
lean::cnstr_set_scalar(x_238, sizeof(void*)*2, x_236);
x_239 = x_238;
return x_239;
}
default:
{
obj* x_240; obj* x_243; obj* x_244; obj* x_245; obj* x_247; uint8 x_248; obj* x_249; obj* x_250; obj* x_251; 
x_240 = lean::cnstr_get(x_0, 0);
lean::inc(x_240);
lean::dec(x_0);
x_243 = l_Nat_repr(x_240);
x_244 = l_Lean_IR_VarId_HasToString___closed__1;
x_245 = lean::string_append(x_244, x_243);
lean::dec(x_243);
x_247 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_247, 0, x_245);
x_248 = 0;
x_249 = l___private_init_lean_compiler_ir_format_5__formatExpr___main___closed__14;
x_250 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_247);
lean::cnstr_set_scalar(x_250, sizeof(void*)*2, x_248);
x_251 = x_250;
return x_251;
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
obj* l_Lean_IR_exprHasToString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___private_init_lean_compiler_ir_format_5__formatExpr___main(x_0);
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Format_pretty(x_1, x_2);
return x_3;
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
x_0 = lean::mk_string("@& ");
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
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::box(0);
x_3 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_0, x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_formatParams(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::box(0);
x_3 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_0, x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_format_2__formatArray___at_Lean_IR_formatParams___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_formatParams___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_formatParams(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_0 = lean::mk_string("inc");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("inc");
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
obj* _init_l_Lean_IR_formatFnBody___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("dec");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("dec");
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
obj* _init_l_Lean_IR_formatFnBody___main___closed__15() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("del ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__16() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("mdata ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__17() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("case ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__18() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" of");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__19() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("ret ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__20() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("jmp ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__21() {
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
x_56 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_42, x_42, x_54, x_55);
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
obj* x_258; obj* x_260; obj* x_262; obj* x_265; uint8 x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_271; obj* x_272; 
x_258 = lean::cnstr_get(x_1, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_1, 1);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_1, 2);
lean::inc(x_262);
lean::dec(x_1);
x_265 = lean::mk_nat_obj(1ul);
x_266 = lean::nat_dec_eq(x_260, x_265);
x_267 = l_Nat_repr(x_258);
x_268 = l_Lean_IR_VarId_HasToString___closed__1;
x_269 = lean::string_append(x_268, x_267);
lean::dec(x_267);
x_271 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_271, 0, x_269);
x_272 = l_Lean_IR_formatFnBody___main(x_0, x_262);
if (x_266 == 0)
{
obj* x_273; obj* x_274; uint8 x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
x_273 = l_Nat_repr(x_260);
x_274 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
x_275 = 0;
x_276 = l_Lean_Format_sbracket___closed__1;
x_277 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_277, 0, x_276);
lean::cnstr_set(x_277, 1, x_274);
lean::cnstr_set_scalar(x_277, sizeof(void*)*2, x_275);
x_278 = x_277;
x_279 = l_Lean_Format_sbracket___closed__2;
x_280 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_280, 0, x_278);
lean::cnstr_set(x_280, 1, x_279);
lean::cnstr_set_scalar(x_280, sizeof(void*)*2, x_275);
x_281 = x_280;
x_282 = l_Lean_Format_sbracket___closed__3;
x_283 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_283, 0, x_282);
lean::cnstr_set(x_283, 1, x_281);
x_284 = l_Lean_Format_group___main(x_283);
x_285 = l_Lean_IR_formatFnBody___main___closed__11;
x_286 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_284);
lean::cnstr_set_scalar(x_286, sizeof(void*)*2, x_275);
x_287 = x_286;
x_288 = l_Lean_Format_flatten___main___closed__1;
x_289 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_289, 0, x_287);
lean::cnstr_set(x_289, 1, x_288);
lean::cnstr_set_scalar(x_289, sizeof(void*)*2, x_275);
x_290 = x_289;
x_291 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_291, 0, x_290);
lean::cnstr_set(x_291, 1, x_271);
lean::cnstr_set_scalar(x_291, sizeof(void*)*2, x_275);
x_292 = x_291;
x_293 = l_Lean_IR_formatFnBody___main___closed__2;
x_294 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_294, 0, x_292);
lean::cnstr_set(x_294, 1, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*2, x_275);
x_295 = x_294;
x_296 = lean::box(1);
x_297 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_297, 0, x_295);
lean::cnstr_set(x_297, 1, x_296);
lean::cnstr_set_scalar(x_297, sizeof(void*)*2, x_275);
x_298 = x_297;
x_299 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_299, 0, x_298);
lean::cnstr_set(x_299, 1, x_272);
lean::cnstr_set_scalar(x_299, sizeof(void*)*2, x_275);
x_300 = x_299;
return x_300;
}
else
{
uint8 x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; 
lean::dec(x_260);
x_302 = 0;
x_303 = l_Lean_IR_formatFnBody___main___closed__12;
x_304 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_304, 0, x_303);
lean::cnstr_set(x_304, 1, x_271);
lean::cnstr_set_scalar(x_304, sizeof(void*)*2, x_302);
x_305 = x_304;
x_306 = l_Lean_IR_formatFnBody___main___closed__2;
x_307 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_307, 0, x_305);
lean::cnstr_set(x_307, 1, x_306);
lean::cnstr_set_scalar(x_307, sizeof(void*)*2, x_302);
x_308 = x_307;
x_309 = lean::box(1);
x_310 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_310, 0, x_308);
lean::cnstr_set(x_310, 1, x_309);
lean::cnstr_set_scalar(x_310, sizeof(void*)*2, x_302);
x_311 = x_310;
x_312 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_272);
lean::cnstr_set_scalar(x_312, sizeof(void*)*2, x_302);
x_313 = x_312;
return x_313;
}
}
case 7:
{
obj* x_314; obj* x_316; obj* x_318; obj* x_321; uint8 x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_327; obj* x_328; 
x_314 = lean::cnstr_get(x_1, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_1, 1);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_1, 2);
lean::inc(x_318);
lean::dec(x_1);
x_321 = lean::mk_nat_obj(1ul);
x_322 = lean::nat_dec_eq(x_316, x_321);
x_323 = l_Nat_repr(x_314);
x_324 = l_Lean_IR_VarId_HasToString___closed__1;
x_325 = lean::string_append(x_324, x_323);
lean::dec(x_323);
x_327 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_327, 0, x_325);
x_328 = l_Lean_IR_formatFnBody___main(x_0, x_318);
if (x_322 == 0)
{
obj* x_329; obj* x_330; uint8 x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; 
x_329 = l_Nat_repr(x_316);
x_330 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_330, 0, x_329);
x_331 = 0;
x_332 = l_Lean_Format_sbracket___closed__1;
x_333 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_333, 0, x_332);
lean::cnstr_set(x_333, 1, x_330);
lean::cnstr_set_scalar(x_333, sizeof(void*)*2, x_331);
x_334 = x_333;
x_335 = l_Lean_Format_sbracket___closed__2;
x_336 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_336, 0, x_334);
lean::cnstr_set(x_336, 1, x_335);
lean::cnstr_set_scalar(x_336, sizeof(void*)*2, x_331);
x_337 = x_336;
x_338 = l_Lean_Format_sbracket___closed__3;
x_339 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_339, 0, x_338);
lean::cnstr_set(x_339, 1, x_337);
x_340 = l_Lean_Format_group___main(x_339);
x_341 = l_Lean_IR_formatFnBody___main___closed__13;
x_342 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_342, 0, x_341);
lean::cnstr_set(x_342, 1, x_340);
lean::cnstr_set_scalar(x_342, sizeof(void*)*2, x_331);
x_343 = x_342;
x_344 = l_Lean_Format_flatten___main___closed__1;
x_345 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_345, 0, x_343);
lean::cnstr_set(x_345, 1, x_344);
lean::cnstr_set_scalar(x_345, sizeof(void*)*2, x_331);
x_346 = x_345;
x_347 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_347, 0, x_346);
lean::cnstr_set(x_347, 1, x_327);
lean::cnstr_set_scalar(x_347, sizeof(void*)*2, x_331);
x_348 = x_347;
x_349 = l_Lean_IR_formatFnBody___main___closed__2;
x_350 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_350, 0, x_348);
lean::cnstr_set(x_350, 1, x_349);
lean::cnstr_set_scalar(x_350, sizeof(void*)*2, x_331);
x_351 = x_350;
x_352 = lean::box(1);
x_353 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_353, 0, x_351);
lean::cnstr_set(x_353, 1, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*2, x_331);
x_354 = x_353;
x_355 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_355, 0, x_354);
lean::cnstr_set(x_355, 1, x_328);
lean::cnstr_set_scalar(x_355, sizeof(void*)*2, x_331);
x_356 = x_355;
return x_356;
}
else
{
uint8 x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; 
lean::dec(x_316);
x_358 = 0;
x_359 = l_Lean_IR_formatFnBody___main___closed__14;
x_360 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_327);
lean::cnstr_set_scalar(x_360, sizeof(void*)*2, x_358);
x_361 = x_360;
x_362 = l_Lean_IR_formatFnBody___main___closed__2;
x_363 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_363, 0, x_361);
lean::cnstr_set(x_363, 1, x_362);
lean::cnstr_set_scalar(x_363, sizeof(void*)*2, x_358);
x_364 = x_363;
x_365 = lean::box(1);
x_366 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_366, 0, x_364);
lean::cnstr_set(x_366, 1, x_365);
lean::cnstr_set_scalar(x_366, sizeof(void*)*2, x_358);
x_367 = x_366;
x_368 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_368, 0, x_367);
lean::cnstr_set(x_368, 1, x_328);
lean::cnstr_set_scalar(x_368, sizeof(void*)*2, x_358);
x_369 = x_368;
return x_369;
}
}
case 8:
{
obj* x_370; obj* x_372; obj* x_375; obj* x_376; obj* x_377; obj* x_379; uint8 x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
x_370 = lean::cnstr_get(x_1, 0);
lean::inc(x_370);
x_372 = lean::cnstr_get(x_1, 1);
lean::inc(x_372);
lean::dec(x_1);
x_375 = l_Nat_repr(x_370);
x_376 = l_Lean_IR_VarId_HasToString___closed__1;
x_377 = lean::string_append(x_376, x_375);
lean::dec(x_375);
x_379 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_379, 0, x_377);
x_380 = 0;
x_381 = l_Lean_IR_formatFnBody___main___closed__15;
x_382 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_382, 0, x_381);
lean::cnstr_set(x_382, 1, x_379);
lean::cnstr_set_scalar(x_382, sizeof(void*)*2, x_380);
x_383 = x_382;
x_384 = l_Lean_IR_formatFnBody___main___closed__2;
x_385 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_385, 0, x_383);
lean::cnstr_set(x_385, 1, x_384);
lean::cnstr_set_scalar(x_385, sizeof(void*)*2, x_380);
x_386 = x_385;
x_387 = lean::box(1);
x_388 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_388, 0, x_386);
lean::cnstr_set(x_388, 1, x_387);
lean::cnstr_set_scalar(x_388, sizeof(void*)*2, x_380);
x_389 = x_388;
x_390 = l_Lean_IR_formatFnBody___main(x_0, x_372);
x_391 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_391, 0, x_389);
lean::cnstr_set(x_391, 1, x_390);
lean::cnstr_set_scalar(x_391, sizeof(void*)*2, x_380);
x_392 = x_391;
return x_392;
}
case 9:
{
obj* x_393; obj* x_395; obj* x_398; uint8 x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; 
x_393 = lean::cnstr_get(x_1, 0);
lean::inc(x_393);
x_395 = lean::cnstr_get(x_1, 1);
lean::inc(x_395);
lean::dec(x_1);
x_398 = l_Lean_formatKVMap(x_393);
x_399 = 0;
x_400 = l_Lean_IR_formatFnBody___main___closed__16;
x_401 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_401, 0, x_400);
lean::cnstr_set(x_401, 1, x_398);
lean::cnstr_set_scalar(x_401, sizeof(void*)*2, x_399);
x_402 = x_401;
x_403 = l_Lean_IR_formatFnBody___main___closed__2;
x_404 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_404, 0, x_402);
lean::cnstr_set(x_404, 1, x_403);
lean::cnstr_set_scalar(x_404, sizeof(void*)*2, x_399);
x_405 = x_404;
x_406 = lean::box(1);
x_407 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_407, 0, x_405);
lean::cnstr_set(x_407, 1, x_406);
lean::cnstr_set_scalar(x_407, sizeof(void*)*2, x_399);
x_408 = x_407;
x_409 = l_Lean_IR_formatFnBody___main(x_0, x_395);
x_410 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_410, 0, x_408);
lean::cnstr_set(x_410, 1, x_409);
lean::cnstr_set_scalar(x_410, sizeof(void*)*2, x_399);
x_411 = x_410;
return x_411;
}
case 10:
{
obj* x_412; obj* x_414; obj* x_417; obj* x_418; obj* x_419; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_433; obj* x_434; 
x_412 = lean::cnstr_get(x_1, 1);
lean::inc(x_412);
x_414 = lean::cnstr_get(x_1, 2);
lean::inc(x_414);
lean::dec(x_1);
x_417 = l_Nat_repr(x_412);
x_418 = l_Lean_IR_VarId_HasToString___closed__1;
x_419 = lean::string_append(x_418, x_417);
lean::dec(x_417);
x_421 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_421, 0, x_419);
x_422 = 0;
x_423 = l_Lean_IR_formatFnBody___main___closed__17;
x_424 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_424, 0, x_423);
lean::cnstr_set(x_424, 1, x_421);
lean::cnstr_set_scalar(x_424, sizeof(void*)*2, x_422);
x_425 = x_424;
x_426 = l_Lean_IR_formatFnBody___main___closed__18;
x_427 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_427, 0, x_425);
lean::cnstr_set(x_427, 1, x_426);
lean::cnstr_set_scalar(x_427, sizeof(void*)*2, x_422);
x_428 = x_427;
x_429 = lean::mk_nat_obj(0ul);
x_430 = lean::box(0);
x_431 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_0, x_414, x_414, x_429, x_430);
lean::dec(x_414);
x_433 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_433, 0, x_428);
lean::cnstr_set(x_433, 1, x_431);
lean::cnstr_set_scalar(x_433, sizeof(void*)*2, x_422);
x_434 = x_433;
return x_434;
}
case 11:
{
obj* x_436; obj* x_439; uint8 x_440; obj* x_441; obj* x_442; obj* x_443; 
lean::dec(x_0);
x_436 = lean::cnstr_get(x_1, 0);
lean::inc(x_436);
lean::dec(x_1);
x_439 = l___private_init_lean_compiler_ir_format_1__formatArg___main(x_436);
x_440 = 0;
x_441 = l_Lean_IR_formatFnBody___main___closed__19;
x_442 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_442, 0, x_441);
lean::cnstr_set(x_442, 1, x_439);
lean::cnstr_set_scalar(x_442, sizeof(void*)*2, x_440);
x_443 = x_442;
return x_443;
}
case 12:
{
obj* x_445; obj* x_447; obj* x_450; obj* x_451; obj* x_452; obj* x_454; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_463; obj* x_464; 
lean::dec(x_0);
x_445 = lean::cnstr_get(x_1, 0);
lean::inc(x_445);
x_447 = lean::cnstr_get(x_1, 1);
lean::inc(x_447);
lean::dec(x_1);
x_450 = l_Nat_repr(x_445);
x_451 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_452 = lean::string_append(x_451, x_450);
lean::dec(x_450);
x_454 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_454, 0, x_452);
x_455 = 0;
x_456 = l_Lean_IR_formatFnBody___main___closed__20;
x_457 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_457, 0, x_456);
lean::cnstr_set(x_457, 1, x_454);
lean::cnstr_set_scalar(x_457, sizeof(void*)*2, x_455);
x_458 = x_457;
x_459 = lean::mk_nat_obj(0ul);
x_460 = lean::box(0);
x_461 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_format_5__formatExpr___main___spec__2(x_447, x_447, x_459, x_460);
lean::dec(x_447);
x_463 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_463, 0, x_458);
lean::cnstr_set(x_463, 1, x_461);
lean::cnstr_set_scalar(x_463, sizeof(void*)*2, x_455);
x_464 = x_463;
return x_464;
}
default:
{
obj* x_466; 
lean::dec(x_0);
x_466 = l_Lean_IR_formatFnBody___main___closed__21;
return x_466;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_0, x_1, x_2, x_3, x_4);
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
x_19 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_17, x_18);
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
x_45 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
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
x_56 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_43, x_43, x_54, x_55);
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
 l_Lean_IR_formatFnBody___main___closed__19 = _init_l_Lean_IR_formatFnBody___main___closed__19();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__19);
 l_Lean_IR_formatFnBody___main___closed__20 = _init_l_Lean_IR_formatFnBody___main___closed__20();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__20);
 l_Lean_IR_formatFnBody___main___closed__21 = _init_l_Lean_IR_formatFnBody___main___closed__21();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__21);
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
