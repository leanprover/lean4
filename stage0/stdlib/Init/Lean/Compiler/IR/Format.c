// Lean compiler output
// Module: Init.Lean.Compiler.IR.Format
// Imports: Init.Lean.Data.Format Init.Lean.Compiler.IR.Basic
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_IR_litValHasFormat___closed__1;
lean_object* l_Lean_IR_typeHasToString;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__15;
lean_object* l_Lean_IR_formatFnBody___main___closed__6;
lean_object* l_Lean_IR_formatFnBodyHead___closed__3;
lean_object* l_Lean_IR_fnBodyHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__29;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
lean_object* l_Lean_IR_formatFnBodyHead___closed__33;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10;
lean_object* l_Lean_IR_formatFnBodyHead___closed__22;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26;
lean_object* l_Lean_IR_formatFnBodyHead___closed__7;
lean_object* l_Lean_IR_formatAlt___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
lean_object* l_Lean_IR_formatFnBodyHead___closed__24;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_IR_formatFnBody___main___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1;
lean_object* l_Lean_IR_formatFnBody___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32;
lean_object* l_Lean_IR_formatAlt___closed__4;
lean_object* l_Lean_IR_formatFnBody___main___closed__5;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam(lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(lean_object*);
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(lean_object*);
lean_object* l_Lean_IR_formatAlt___closed__2;
lean_object* l_Lean_IR_formatFnBodyHead___closed__11;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4;
lean_object* l_Lean_IR_formatFnBodyHead___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_argHasFormat___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4;
lean_object* l_Lean_IR_formatArray___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_IR_declHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__23;
lean_object* l_Lean_IR_formatFnBody___main___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17;
lean_object* l_Lean_IR_formatFnBodyHead___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6;
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__17;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17;
lean_object* l_Lean_IR_formatFnBodyHead___closed__6;
lean_object* l_Lean_IR_litValHasFormat;
lean_object* l_Lean_IR_formatParams___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15;
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__16;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5;
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31;
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_IR_formatDecl___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27;
lean_object* l_Lean_IR_formatArray(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9;
lean_object* l_Lean_IR_formatFnBodyHead___closed__37;
lean_object* l_Lean_IR_formatFnBody___main___closed__2;
lean_object* l_Lean_IR_formatFnBody___main___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19;
lean_object* l_Lean_IR_formatDecl___closed__1;
lean_object* l_Lean_IR_formatDecl___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3;
lean_object* l_Lean_formatKVMap(lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_declHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__20;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___boxed(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_IR_exprHasFormat___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ctorInfoHasFormat___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___boxed(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__26;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14;
lean_object* l_Lean_IR_typeHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__31;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
lean_object* lean_ir_decl_to_string(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__27;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25;
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1;
lean_object* l_Lean_IR_fnBodyHasToString(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13;
lean_object* l_Lean_IR_formatFnBodyHead___closed__25;
lean_object* lean_ir_format_fn_body_head(lean_object*);
extern lean_object* l_PersistentArray_Stats_toString___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2;
lean_object* l_Lean_IR_formatAlt___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__34;
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2;
lean_object* l_Lean_IR_ctorInfoHasFormat;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__13;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
lean_object* l_Lean_IR_argHasFormat;
lean_object* l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13;
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_IR_formatFnBodyHead___closed__5;
lean_object* l_Lean_IR_formatFnBodyHead___closed__30;
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23;
lean_object* l_Lean_IR_paramHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__28;
lean_object* l_Lean_IR_formatFnBodyHead___closed__14;
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_IR_paramHasFormat___closed__1;
lean_object* l_Lean_IR_declHasToString;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7;
lean_object* l_Lean_IR_formatDecl___closed__4;
lean_object* l_Lean_IR_typeHasToString___closed__1;
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3;
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15;
lean_object* l_Lean_IR_formatParams(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_2__formatLitVal(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__10;
lean_object* l_Lean_IR_formatFnBodyHead___closed__32;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_IR_typeHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__12;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__4;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_exprHasFormat;
lean_object* l_Lean_IR_fnBodyHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
lean_object* l_Lean_IR_declHasToString___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22;
lean_object* l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__19;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__36;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24;
lean_object* l_Lean_IR_exprHasToString(lean_object*);
lean_object* l_Lean_IR_formatFnBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__35;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__21;
lean_object* l_Lean_IR_formatFnBodyHead___closed__38;
lean_object* l_Lean_IR_formatArray___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatAlt(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__2;
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("◾");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_IR_VarId_HasToString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2;
return x_7;
}
}
}
lean_object* _init_l_Lean_IR_argHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_Format_1__formatArg), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_argHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_argHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint32_t x_11; uint16_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint16_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
x_10 = l_Lean_Format_flatten___main___closed__1;
x_11 = 0;
x_12 = 0;
x_13 = 0;
x_14 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_11);
lean_ctor_set_uint16(x_14, sizeof(void*)*2 + 4, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 7, x_13);
lean_inc(x_1);
x_15 = lean_apply_1(x_1, x_8);
x_16 = 0;
x_17 = 0;
x_18 = 0;
x_19 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_uint16(x_19, sizeof(void*)*2 + 4, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 7, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_IR_formatArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(x_1, x_2, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_formatArray___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_formatArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_formatArray___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_2__formatLitVal(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_quote(x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* _init_l_Lean_IR_litValHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_Format_2__formatLitVal), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_litValHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_litValHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ctor_");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_toString___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint32_t x_10; uint16_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Nat_repr(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = 0;
x_9 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2;
x_10 = 0;
x_11 = 0;
x_12 = 0;
x_13 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_13, sizeof(void*)*2, x_10);
lean_ctor_set_uint16(x_13, sizeof(void*)*2 + 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 7, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_4);
x_16 = lean_box(0);
x_17 = lean_name_eq(x_2, x_16);
if (x_15 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_14, x_5);
if (x_18 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
if (x_17 == 0)
{
lean_object* x_19; uint32_t x_20; uint16_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint16_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; uint16_t x_33; uint8_t x_34; lean_object* x_35; 
x_19 = l_Lean_Format_sbracket___closed__2;
x_20 = 0;
x_21 = 0;
x_22 = 0;
x_23 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_23, sizeof(void*)*2, x_20);
lean_ctor_set_uint16(x_23, sizeof(void*)*2 + 4, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 7, x_22);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_2);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = 0;
x_28 = 0;
x_29 = 0;
x_30 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_uint16(x_30, sizeof(void*)*2 + 4, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 7, x_29);
x_31 = l_Lean_Format_sbracket___closed__3;
x_32 = 0;
x_33 = 0;
x_34 = 0;
x_35 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_35, sizeof(void*)*2, x_32);
lean_ctor_set_uint16(x_35, sizeof(void*)*2 + 4, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 7, x_34);
return x_35;
}
else
{
lean_dec(x_2);
return x_13;
}
}
else
{
lean_object* x_36; uint32_t x_37; uint16_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint16_t x_44; uint8_t x_45; lean_object* x_46; uint32_t x_47; uint16_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; uint16_t x_54; uint8_t x_55; lean_object* x_56; 
x_36 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
x_37 = 0;
x_38 = 0;
x_39 = 0;
x_40 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_40, sizeof(void*)*2, x_37);
lean_ctor_set_uint16(x_40, sizeof(void*)*2 + 4, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 7, x_39);
x_41 = l_Nat_repr(x_4);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = 0;
x_44 = 0;
x_45 = 0;
x_46 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_uint16(x_46, sizeof(void*)*2 + 4, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 7, x_45);
x_47 = 0;
x_48 = 0;
x_49 = 0;
x_50 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set_uint8(x_50, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_50, sizeof(void*)*2, x_47);
lean_ctor_set_uint16(x_50, sizeof(void*)*2 + 4, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2 + 7, x_49);
x_51 = l_Nat_repr(x_5);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = 0;
x_54 = 0;
x_55 = 0;
x_56 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_56, sizeof(void*)*2, x_53);
lean_ctor_set_uint16(x_56, sizeof(void*)*2 + 4, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 7, x_55);
if (x_17 == 0)
{
lean_object* x_57; uint32_t x_58; uint16_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint32_t x_65; uint16_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; lean_object* x_73; 
x_57 = l_Lean_Format_sbracket___closed__2;
x_58 = 0;
x_59 = 0;
x_60 = 0;
x_61 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_61, sizeof(void*)*2, x_58);
lean_ctor_set_uint16(x_61, sizeof(void*)*2 + 4, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 7, x_60);
x_62 = l_Lean_Name_toString___closed__1;
x_63 = l_Lean_Name_toStringWithSep___main(x_62, x_2);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = 0;
x_66 = 0;
x_67 = 0;
x_68 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_68, sizeof(void*)*2, x_65);
lean_ctor_set_uint16(x_68, sizeof(void*)*2 + 4, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 7, x_67);
x_69 = l_Lean_Format_sbracket___closed__3;
x_70 = 0;
x_71 = 0;
x_72 = 0;
x_73 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_73, sizeof(void*)*2, x_70);
lean_ctor_set_uint16(x_73, sizeof(void*)*2 + 4, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 7, x_72);
return x_73;
}
else
{
lean_dec(x_2);
return x_56;
}
}
}
else
{
lean_object* x_74; uint32_t x_75; uint16_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint32_t x_81; uint16_t x_82; uint8_t x_83; lean_object* x_84; uint32_t x_85; uint16_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint32_t x_91; uint16_t x_92; uint8_t x_93; lean_object* x_94; 
x_74 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
x_75 = 0;
x_76 = 0;
x_77 = 0;
x_78 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_78, 0, x_13);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_78, sizeof(void*)*2, x_75);
lean_ctor_set_uint16(x_78, sizeof(void*)*2 + 4, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 7, x_77);
x_79 = l_Nat_repr(x_4);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = 0;
x_82 = 0;
x_83 = 0;
x_84 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_84, sizeof(void*)*2, x_81);
lean_ctor_set_uint16(x_84, sizeof(void*)*2 + 4, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 7, x_83);
x_85 = 0;
x_86 = 0;
x_87 = 0;
x_88 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_74);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_88, sizeof(void*)*2, x_85);
lean_ctor_set_uint16(x_88, sizeof(void*)*2 + 4, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 7, x_87);
x_89 = l_Nat_repr(x_5);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = 0;
x_92 = 0;
x_93 = 0;
x_94 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_94, sizeof(void*)*2, x_91);
lean_ctor_set_uint16(x_94, sizeof(void*)*2 + 4, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 7, x_93);
if (x_17 == 0)
{
lean_object* x_95; uint32_t x_96; uint16_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint32_t x_103; uint16_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; uint32_t x_108; uint16_t x_109; uint8_t x_110; lean_object* x_111; 
x_95 = l_Lean_Format_sbracket___closed__2;
x_96 = 0;
x_97 = 0;
x_98 = 0;
x_99 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_99, sizeof(void*)*2, x_96);
lean_ctor_set_uint16(x_99, sizeof(void*)*2 + 4, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 7, x_98);
x_100 = l_Lean_Name_toString___closed__1;
x_101 = l_Lean_Name_toStringWithSep___main(x_100, x_2);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = 0;
x_104 = 0;
x_105 = 0;
x_106 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_102);
lean_ctor_set_uint8(x_106, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_106, sizeof(void*)*2, x_103);
lean_ctor_set_uint16(x_106, sizeof(void*)*2 + 4, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*2 + 7, x_105);
x_107 = l_Lean_Format_sbracket___closed__3;
x_108 = 0;
x_109 = 0;
x_110 = 0;
x_111 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set_uint8(x_111, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_111, sizeof(void*)*2, x_108);
lean_ctor_set_uint16(x_111, sizeof(void*)*2 + 4, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*2 + 7, x_110);
return x_111;
}
else
{
lean_dec(x_2);
return x_94;
}
}
}
}
lean_object* _init_l_Lean_IR_ctorInfoHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_ctorInfoHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ctorInfoHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint32_t x_10; uint16_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint16_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = 0;
x_11 = 0;
x_12 = 0;
x_13 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_13, sizeof(void*)*2, x_10);
lean_ctor_set_uint16(x_13, sizeof(void*)*2 + 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 7, x_12);
x_14 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_7);
x_15 = 0;
x_16 = 0;
x_17 = 0;
x_18 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_18, sizeof(void*)*2, x_15);
lean_ctor_set_uint16(x_18, sizeof(void*)*2 + 4, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 7, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reset[");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reuse");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
x_3 = l_Lean_Format_join___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("!");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
x_3 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj[");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uproj[");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sproj[");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pap ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("box ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unbox ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isShared ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isTaggedPtr ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint32_t x_9; uint16_t x_10; uint8_t x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_3, x_3, x_5, x_6);
lean_dec(x_3);
x_8 = 0;
x_9 = 0;
x_10 = 0;
x_11 = 0;
x_12 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_12, sizeof(void*)*2, x_9);
lean_ctor_set_uint16(x_12, sizeof(void*)*2 + 4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2 + 7, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint32_t x_19; uint16_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint16_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; uint16_t x_33; uint8_t x_34; lean_object* x_35; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Nat_repr(x_13);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = 0;
x_18 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2;
x_19 = 0;
x_20 = 0;
x_21 = 0;
x_22 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 6, x_17);
lean_ctor_set_uint32(x_22, sizeof(void*)*2, x_19);
lean_ctor_set_uint16(x_22, sizeof(void*)*2 + 4, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 7, x_21);
x_23 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_24 = 0;
x_25 = 0;
x_26 = 0;
x_27 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 6, x_17);
lean_ctor_set_uint32(x_27, sizeof(void*)*2, x_24);
lean_ctor_set_uint16(x_27, sizeof(void*)*2 + 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 7, x_26);
x_28 = l_Nat_repr(x_14);
x_29 = l_Lean_IR_VarId_HasToString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = 0;
x_33 = 0;
x_34 = 0;
x_35 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 6, x_17);
lean_ctor_set_uint32(x_35, sizeof(void*)*2, x_32);
lean_ctor_set_uint16(x_35, sizeof(void*)*2 + 4, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 7, x_34);
return x_35;
}
case 2:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 6);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Nat_repr(x_36);
x_41 = l_Lean_IR_VarId_HasToString___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(x_37);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_box(0);
x_47 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_39, x_39, x_45, x_46);
lean_dec(x_39);
if (x_38 == 0)
{
uint8_t x_48; lean_object* x_49; uint32_t x_50; uint16_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; uint16_t x_56; uint8_t x_57; lean_object* x_58; uint32_t x_59; uint16_t x_60; uint8_t x_61; lean_object* x_62; uint32_t x_63; uint16_t x_64; uint8_t x_65; lean_object* x_66; 
x_48 = 0;
x_49 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10;
x_50 = 0;
x_51 = 0;
x_52 = 0;
x_53 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 6, x_48);
lean_ctor_set_uint32(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_uint16(x_53, sizeof(void*)*2 + 4, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 7, x_52);
x_54 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
x_55 = 0;
x_56 = 0;
x_57 = 0;
x_58 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 6, x_48);
lean_ctor_set_uint32(x_58, sizeof(void*)*2, x_55);
lean_ctor_set_uint16(x_58, sizeof(void*)*2 + 4, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 7, x_57);
x_59 = 0;
x_60 = 0;
x_61 = 0;
x_62 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set_uint8(x_62, sizeof(void*)*2 + 6, x_48);
lean_ctor_set_uint32(x_62, sizeof(void*)*2, x_59);
lean_ctor_set_uint16(x_62, sizeof(void*)*2 + 4, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*2 + 7, x_61);
x_63 = 0;
x_64 = 0;
x_65 = 0;
x_66 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_47);
lean_ctor_set_uint8(x_66, sizeof(void*)*2 + 6, x_48);
lean_ctor_set_uint32(x_66, sizeof(void*)*2, x_63);
lean_ctor_set_uint16(x_66, sizeof(void*)*2 + 4, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*2 + 7, x_65);
return x_66;
}
else
{
uint8_t x_67; lean_object* x_68; uint32_t x_69; uint16_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint32_t x_74; uint16_t x_75; uint8_t x_76; lean_object* x_77; uint32_t x_78; uint16_t x_79; uint8_t x_80; lean_object* x_81; uint32_t x_82; uint16_t x_83; uint8_t x_84; lean_object* x_85; 
x_67 = 0;
x_68 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14;
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_43);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 6, x_67);
lean_ctor_set_uint32(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_uint16(x_72, sizeof(void*)*2 + 4, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 7, x_71);
x_73 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
x_74 = 0;
x_75 = 0;
x_76 = 0;
x_77 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 6, x_67);
lean_ctor_set_uint32(x_77, sizeof(void*)*2, x_74);
lean_ctor_set_uint16(x_77, sizeof(void*)*2 + 4, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 7, x_76);
x_78 = 0;
x_79 = 0;
x_80 = 0;
x_81 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_44);
lean_ctor_set_uint8(x_81, sizeof(void*)*2 + 6, x_67);
lean_ctor_set_uint32(x_81, sizeof(void*)*2, x_78);
lean_ctor_set_uint16(x_81, sizeof(void*)*2 + 4, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*2 + 7, x_80);
x_82 = 0;
x_83 = 0;
x_84 = 0;
x_85 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 6, x_67);
lean_ctor_set_uint32(x_85, sizeof(void*)*2, x_82);
lean_ctor_set_uint16(x_85, sizeof(void*)*2 + 4, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 7, x_84);
return x_85;
}
}
case 3:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint32_t x_92; uint16_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; uint32_t x_97; uint16_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint32_t x_105; uint16_t x_106; uint8_t x_107; lean_object* x_108; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
lean_dec(x_1);
x_88 = l_Nat_repr(x_86);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = 0;
x_91 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16;
x_92 = 0;
x_93 = 0;
x_94 = 0;
x_95 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 6, x_90);
lean_ctor_set_uint32(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_uint16(x_95, sizeof(void*)*2 + 4, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 7, x_94);
x_96 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_97 = 0;
x_98 = 0;
x_99 = 0;
x_100 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set_uint8(x_100, sizeof(void*)*2 + 6, x_90);
lean_ctor_set_uint32(x_100, sizeof(void*)*2, x_97);
lean_ctor_set_uint16(x_100, sizeof(void*)*2 + 4, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*2 + 7, x_99);
x_101 = l_Nat_repr(x_87);
x_102 = l_Lean_IR_VarId_HasToString___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = 0;
x_106 = 0;
x_107 = 0;
x_108 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_108, 0, x_100);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set_uint8(x_108, sizeof(void*)*2 + 6, x_90);
lean_ctor_set_uint32(x_108, sizeof(void*)*2, x_105);
lean_ctor_set_uint16(x_108, sizeof(void*)*2 + 4, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*2 + 7, x_107);
return x_108;
}
case 4:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint32_t x_115; uint16_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; uint32_t x_120; uint16_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint32_t x_128; uint16_t x_129; uint8_t x_130; lean_object* x_131; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
lean_dec(x_1);
x_111 = l_Nat_repr(x_109);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = 0;
x_114 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18;
x_115 = 0;
x_116 = 0;
x_117 = 0;
x_118 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*2 + 6, x_113);
lean_ctor_set_uint32(x_118, sizeof(void*)*2, x_115);
lean_ctor_set_uint16(x_118, sizeof(void*)*2 + 4, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*2 + 7, x_117);
x_119 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_120 = 0;
x_121 = 0;
x_122 = 0;
x_123 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_119);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 6, x_113);
lean_ctor_set_uint32(x_123, sizeof(void*)*2, x_120);
lean_ctor_set_uint16(x_123, sizeof(void*)*2 + 4, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 7, x_122);
x_124 = l_Nat_repr(x_110);
x_125 = l_Lean_IR_VarId_HasToString___closed__1;
x_126 = lean_string_append(x_125, x_124);
lean_dec(x_124);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = 0;
x_129 = 0;
x_130 = 0;
x_131 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_131, 0, x_123);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set_uint8(x_131, sizeof(void*)*2 + 6, x_113);
lean_ctor_set_uint32(x_131, sizeof(void*)*2, x_128);
lean_ctor_set_uint16(x_131, sizeof(void*)*2 + 4, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*2 + 7, x_130);
return x_131;
}
case 5:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; uint32_t x_139; uint16_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint32_t x_144; uint16_t x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; uint32_t x_155; uint16_t x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint32_t x_163; uint16_t x_164; uint8_t x_165; lean_object* x_166; 
x_132 = lean_ctor_get(x_1, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 2);
lean_inc(x_134);
lean_dec(x_1);
x_135 = l_Nat_repr(x_132);
x_136 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = 0;
x_138 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20;
x_139 = 0;
x_140 = 0;
x_141 = 0;
x_142 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_136);
lean_ctor_set_uint8(x_142, sizeof(void*)*2 + 6, x_137);
lean_ctor_set_uint32(x_142, sizeof(void*)*2, x_139);
lean_ctor_set_uint16(x_142, sizeof(void*)*2 + 4, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*2 + 7, x_141);
x_143 = l_Lean_formatKVMap___closed__1;
x_144 = 0;
x_145 = 0;
x_146 = 0;
x_147 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set_uint8(x_147, sizeof(void*)*2 + 6, x_137);
lean_ctor_set_uint32(x_147, sizeof(void*)*2, x_144);
lean_ctor_set_uint16(x_147, sizeof(void*)*2 + 4, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*2 + 7, x_146);
x_148 = l_Nat_repr(x_133);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = 0;
x_151 = 0;
x_152 = 0;
x_153 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set_uint8(x_153, sizeof(void*)*2 + 6, x_137);
lean_ctor_set_uint32(x_153, sizeof(void*)*2, x_150);
lean_ctor_set_uint16(x_153, sizeof(void*)*2 + 4, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*2 + 7, x_152);
x_154 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_155 = 0;
x_156 = 0;
x_157 = 0;
x_158 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*2 + 6, x_137);
lean_ctor_set_uint32(x_158, sizeof(void*)*2, x_155);
lean_ctor_set_uint16(x_158, sizeof(void*)*2 + 4, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*2 + 7, x_157);
x_159 = l_Nat_repr(x_134);
x_160 = l_Lean_IR_VarId_HasToString___closed__1;
x_161 = lean_string_append(x_160, x_159);
lean_dec(x_159);
x_162 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = 0;
x_164 = 0;
x_165 = 0;
x_166 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_166, 0, x_158);
lean_ctor_set(x_166, 1, x_162);
lean_ctor_set_uint8(x_166, sizeof(void*)*2 + 6, x_137);
lean_ctor_set_uint32(x_166, sizeof(void*)*2, x_163);
lean_ctor_set_uint16(x_166, sizeof(void*)*2 + 4, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*2 + 7, x_165);
return x_166;
}
case 6:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint32_t x_176; uint16_t x_177; uint8_t x_178; lean_object* x_179; 
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 1);
lean_inc(x_168);
lean_dec(x_1);
x_169 = l_Lean_Name_toString___closed__1;
x_170 = l_Lean_Name_toStringWithSep___main(x_169, x_167);
x_171 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_box(0);
x_174 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_168, x_168, x_172, x_173);
lean_dec(x_168);
x_175 = 0;
x_176 = 0;
x_177 = 0;
x_178 = 0;
x_179 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_174);
lean_ctor_set_uint8(x_179, sizeof(void*)*2 + 6, x_175);
lean_ctor_set_uint32(x_179, sizeof(void*)*2, x_176);
lean_ctor_set_uint16(x_179, sizeof(void*)*2 + 4, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*2 + 7, x_178);
return x_179;
}
case 7:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; uint32_t x_187; uint16_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint32_t x_194; uint16_t x_195; uint8_t x_196; lean_object* x_197; 
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_1, 1);
lean_inc(x_181);
lean_dec(x_1);
x_182 = l_Lean_Name_toString___closed__1;
x_183 = l_Lean_Name_toStringWithSep___main(x_182, x_180);
x_184 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = 0;
x_186 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22;
x_187 = 0;
x_188 = 0;
x_189 = 0;
x_190 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_190, 0, x_186);
lean_ctor_set(x_190, 1, x_184);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 6, x_185);
lean_ctor_set_uint32(x_190, sizeof(void*)*2, x_187);
lean_ctor_set_uint16(x_190, sizeof(void*)*2 + 4, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 7, x_189);
x_191 = lean_unsigned_to_nat(0u);
x_192 = lean_box(0);
x_193 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_181, x_181, x_191, x_192);
lean_dec(x_181);
x_194 = 0;
x_195 = 0;
x_196 = 0;
x_197 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set_uint8(x_197, sizeof(void*)*2 + 6, x_185);
lean_ctor_set_uint32(x_197, sizeof(void*)*2, x_194);
lean_ctor_set_uint16(x_197, sizeof(void*)*2 + 4, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*2 + 7, x_196);
return x_197;
}
case 8:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint32_t x_206; uint16_t x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint32_t x_213; uint16_t x_214; uint8_t x_215; lean_object* x_216; 
x_198 = lean_ctor_get(x_1, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_1, 1);
lean_inc(x_199);
lean_dec(x_1);
x_200 = l_Nat_repr(x_198);
x_201 = l_Lean_IR_VarId_HasToString___closed__1;
x_202 = lean_string_append(x_201, x_200);
lean_dec(x_200);
x_203 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = 0;
x_205 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24;
x_206 = 0;
x_207 = 0;
x_208 = 0;
x_209 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_209, 0, x_205);
lean_ctor_set(x_209, 1, x_203);
lean_ctor_set_uint8(x_209, sizeof(void*)*2 + 6, x_204);
lean_ctor_set_uint32(x_209, sizeof(void*)*2, x_206);
lean_ctor_set_uint16(x_209, sizeof(void*)*2 + 4, x_207);
lean_ctor_set_uint8(x_209, sizeof(void*)*2 + 7, x_208);
x_210 = lean_unsigned_to_nat(0u);
x_211 = lean_box(0);
x_212 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_199, x_199, x_210, x_211);
lean_dec(x_199);
x_213 = 0;
x_214 = 0;
x_215 = 0;
x_216 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_216, 0, x_209);
lean_ctor_set(x_216, 1, x_212);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 6, x_204);
lean_ctor_set_uint32(x_216, sizeof(void*)*2, x_213);
lean_ctor_set_uint16(x_216, sizeof(void*)*2 + 4, x_214);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 7, x_215);
return x_216;
}
case 9:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; uint32_t x_224; uint16_t x_225; uint8_t x_226; lean_object* x_227; 
x_217 = lean_ctor_get(x_1, 1);
lean_inc(x_217);
lean_dec(x_1);
x_218 = l_Nat_repr(x_217);
x_219 = l_Lean_IR_VarId_HasToString___closed__1;
x_220 = lean_string_append(x_219, x_218);
lean_dec(x_218);
x_221 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = 0;
x_223 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26;
x_224 = 0;
x_225 = 0;
x_226 = 0;
x_227 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_221);
lean_ctor_set_uint8(x_227, sizeof(void*)*2 + 6, x_222);
lean_ctor_set_uint32(x_227, sizeof(void*)*2, x_224);
lean_ctor_set_uint16(x_227, sizeof(void*)*2 + 4, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*2 + 7, x_226);
return x_227;
}
case 10:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; uint32_t x_235; uint16_t x_236; uint8_t x_237; lean_object* x_238; 
x_228 = lean_ctor_get(x_1, 0);
lean_inc(x_228);
lean_dec(x_1);
x_229 = l_Nat_repr(x_228);
x_230 = l_Lean_IR_VarId_HasToString___closed__1;
x_231 = lean_string_append(x_230, x_229);
lean_dec(x_229);
x_232 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_233 = 0;
x_234 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28;
x_235 = 0;
x_236 = 0;
x_237 = 0;
x_238 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_232);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 6, x_233);
lean_ctor_set_uint32(x_238, sizeof(void*)*2, x_235);
lean_ctor_set_uint16(x_238, sizeof(void*)*2 + 4, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 7, x_237);
return x_238;
}
case 11:
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_1, 0);
lean_inc(x_239);
lean_dec(x_1);
x_240 = l___private_Init_Lean_Compiler_IR_Format_2__formatLitVal(x_239);
return x_240;
}
case 12:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; uint32_t x_248; uint16_t x_249; uint8_t x_250; lean_object* x_251; 
x_241 = lean_ctor_get(x_1, 0);
lean_inc(x_241);
lean_dec(x_1);
x_242 = l_Nat_repr(x_241);
x_243 = l_Lean_IR_VarId_HasToString___closed__1;
x_244 = lean_string_append(x_243, x_242);
lean_dec(x_242);
x_245 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = 0;
x_247 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30;
x_248 = 0;
x_249 = 0;
x_250 = 0;
x_251 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_251, 0, x_247);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set_uint8(x_251, sizeof(void*)*2 + 6, x_246);
lean_ctor_set_uint32(x_251, sizeof(void*)*2, x_248);
lean_ctor_set_uint16(x_251, sizeof(void*)*2 + 4, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*2 + 7, x_250);
return x_251;
}
default: 
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint32_t x_259; uint16_t x_260; uint8_t x_261; lean_object* x_262; 
x_252 = lean_ctor_get(x_1, 0);
lean_inc(x_252);
lean_dec(x_1);
x_253 = l_Nat_repr(x_252);
x_254 = l_Lean_IR_VarId_HasToString___closed__1;
x_255 = lean_string_append(x_254, x_253);
lean_dec(x_253);
x_256 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = 0;
x_258 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32;
x_259 = 0;
x_260 = 0;
x_261 = 0;
x_262 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_262, 0, x_258);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set_uint8(x_262, sizeof(void*)*2 + 6, x_257);
lean_ctor_set_uint32(x_262, sizeof(void*)*2, x_259);
lean_ctor_set_uint16(x_262, sizeof(void*)*2 + 4, x_260);
lean_ctor_set_uint8(x_262, sizeof(void*)*2 + 7, x_261);
return x_262;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_exprHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_exprHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_exprHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_exprHasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(x_1);
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Format_pretty(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint32_t x_10; uint16_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint16_t x_16; uint8_t x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_7);
x_9 = 0;
x_10 = 0;
x_11 = 0;
x_12 = 0;
lean_inc(x_2);
x_13 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_13, sizeof(void*)*2, x_10);
lean_ctor_set_uint16(x_13, sizeof(void*)*2 + 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 7, x_12);
x_14 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_4, x_2);
x_15 = 0;
x_16 = 0;
x_17 = 0;
x_18 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_18, sizeof(void*)*2, x_15);
lean_ctor_set_uint16(x_18, sizeof(void*)*2 + 4, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 7, x_17);
return x_18;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("float");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u8");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u16");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u32");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u64");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("usize");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("obj");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tobj");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("struct ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PersistentArray_Stats_toString___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("union ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16;
return x_10;
}
case 9:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint32_t x_17; uint16_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; uint16_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; uint16_t x_31; uint8_t x_32; lean_object* x_33; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Array_toList___rarg(x_11);
x_13 = l_Lean_formatKVMap___closed__1;
x_14 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_12, x_13);
lean_dec(x_12);
x_15 = 0;
x_16 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_17 = 0;
x_18 = 0;
x_19 = 0;
x_20 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 6, x_15);
lean_ctor_set_uint32(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_uint16(x_20, sizeof(void*)*2 + 4, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 7, x_19);
x_21 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_22 = 0;
x_23 = 0;
x_24 = 0;
x_25 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 6, x_15);
lean_ctor_set_uint32(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_uint16(x_25, sizeof(void*)*2 + 4, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 7, x_24);
x_26 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_format_group(x_27);
x_29 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18;
x_30 = 0;
x_31 = 0;
x_32 = 0;
x_33 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 6, x_15);
lean_ctor_set_uint32(x_33, sizeof(void*)*2, x_30);
lean_ctor_set_uint16(x_33, sizeof(void*)*2 + 4, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 7, x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint16_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; uint16_t x_54; uint8_t x_55; lean_object* x_56; 
x_34 = lean_ctor_get(x_1, 1);
x_35 = l_Array_toList___rarg(x_34);
x_36 = l_Lean_formatKVMap___closed__1;
x_37 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_35, x_36);
lean_dec(x_35);
x_38 = 0;
x_39 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 6, x_38);
lean_ctor_set_uint32(x_43, sizeof(void*)*2, x_40);
lean_ctor_set_uint16(x_43, sizeof(void*)*2 + 4, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 7, x_42);
x_44 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 6, x_38);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_uint16(x_48, sizeof(void*)*2 + 4, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 7, x_47);
x_49 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
x_50 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_format_group(x_50);
x_52 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23;
x_53 = 0;
x_54 = 0;
x_55 = 0;
x_56 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 6, x_38);
lean_ctor_set_uint32(x_56, sizeof(void*)*2, x_53);
lean_ctor_set_uint16(x_56, sizeof(void*)*2 + 4, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 7, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_typeHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_typeHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_typeHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_typeHasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_IR_typeHasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_typeHasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_typeHasToString___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@& ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint32_t x_11; uint16_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint16_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Nat_repr(x_2);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = 0;
x_10 = l_Lean_Format_paren___closed__2;
x_11 = 0;
x_12 = 0;
x_13 = 0;
x_14 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_11);
lean_ctor_set_uint16(x_14, sizeof(void*)*2 + 4, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 7, x_13);
x_15 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_16 = 0;
x_17 = 0;
x_18 = 0;
x_19 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_uint16(x_19, sizeof(void*)*2 + 4, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 7, x_18);
x_20 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_4);
lean_dec(x_4);
if (x_3 == 0)
{
lean_object* x_21; uint32_t x_22; uint16_t x_23; uint8_t x_24; lean_object* x_25; uint32_t x_26; uint16_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint16_t x_32; uint8_t x_33; lean_object* x_34; 
x_21 = l_Lean_Format_join___closed__1;
x_22 = 0;
x_23 = 0;
x_24 = 0;
x_25 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_uint16(x_25, sizeof(void*)*2 + 4, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 7, x_24);
x_26 = 0;
x_27 = 0;
x_28 = 0;
x_29 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_29, sizeof(void*)*2, x_26);
lean_ctor_set_uint16(x_29, sizeof(void*)*2 + 4, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 7, x_28);
x_30 = l_Lean_Format_paren___closed__3;
x_31 = 0;
x_32 = 0;
x_33 = 0;
x_34 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_34, sizeof(void*)*2, x_31);
lean_ctor_set_uint16(x_34, sizeof(void*)*2 + 4, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 7, x_33);
return x_34;
}
else
{
lean_object* x_35; uint32_t x_36; uint16_t x_37; uint8_t x_38; lean_object* x_39; uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint16_t x_46; uint8_t x_47; lean_object* x_48; 
x_35 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4;
x_36 = 0;
x_37 = 0;
x_38 = 0;
x_39 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_36);
lean_ctor_set_uint16(x_39, sizeof(void*)*2 + 4, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 7, x_38);
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_20);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_43, sizeof(void*)*2, x_40);
lean_ctor_set_uint16(x_43, sizeof(void*)*2 + 4, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 7, x_42);
x_44 = l_Lean_Format_paren___closed__3;
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_uint16(x_48, sizeof(void*)*2 + 4, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 7, x_47);
return x_48;
}
}
}
lean_object* _init_l_Lean_IR_paramHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_Format_6__formatParam), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_paramHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_paramHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" →");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatAlt___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("default →");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatAlt___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint32_t x_12; uint16_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; uint16_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint16_t x_24; uint8_t x_25; lean_object* x_26; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_IR_formatAlt___closed__2;
x_12 = 0;
x_13 = 0;
x_14 = 0;
x_15 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_15, sizeof(void*)*2, x_12);
lean_ctor_set_uint16(x_15, sizeof(void*)*2 + 4, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 7, x_14);
x_16 = lean_apply_1(x_1, x_5);
x_17 = lean_box(1);
x_18 = 0;
x_19 = 0;
x_20 = 0;
x_21 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_21, sizeof(void*)*2, x_18);
lean_ctor_set_uint16(x_21, sizeof(void*)*2 + 4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 7, x_20);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = 0;
x_24 = 0;
x_25 = 0;
x_26 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_uint16(x_26, sizeof(void*)*2 + 4, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 7, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint32_t x_31; uint16_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint32_t x_37; uint16_t x_38; uint8_t x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
lean_dec(x_3);
x_28 = lean_apply_1(x_1, x_27);
x_29 = 0;
x_30 = lean_box(1);
x_31 = 0;
x_32 = 0;
x_33 = 0;
x_34 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 6, x_29);
lean_ctor_set_uint32(x_34, sizeof(void*)*2, x_31);
lean_ctor_set_uint16(x_34, sizeof(void*)*2 + 4, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 7, x_33);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_IR_formatAlt___closed__4;
x_37 = 0;
x_38 = 0;
x_39 = 0;
x_40 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 6, x_29);
lean_ctor_set_uint32(x_40, sizeof(void*)*2, x_37);
lean_ctor_set_uint16(x_40, sizeof(void*)*2 + 4, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 7, x_39);
return x_40;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint32_t x_10; uint16_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint16_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = 0;
x_11 = 0;
x_12 = 0;
x_13 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_13, sizeof(void*)*2, x_10);
lean_ctor_set_uint16(x_13, sizeof(void*)*2 + 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 7, x_12);
x_14 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam(x_7);
x_15 = 0;
x_16 = 0;
x_17 = 0;
x_18 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 6, x_8);
lean_ctor_set_uint32(x_18, sizeof(void*)*2, x_15);
lean_ctor_set_uint16(x_18, sizeof(void*)*2 + 4, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 7, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_formatParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatParams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ...");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("set ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] := ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("setTag ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uset ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sset ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] : ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inc");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__19() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__18;
x_3 = l_Lean_Format_join___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__20() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__19;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dec");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__23() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__22;
x_3 = l_Lean_Format_join___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__24() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__23;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("del ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__29;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" of ...");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ret ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jmp ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__35;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⊥");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__37;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* lean_ir_format_fn_body_head(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint32_t x_11; uint16_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint16_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; uint16_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint16_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint16_t x_32; uint8_t x_33; lean_object* x_34; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Nat_repr(x_2);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = 0;
x_10 = l_Lean_IR_formatFnBodyHead___closed__2;
x_11 = 0;
x_12 = 0;
x_13 = 0;
x_14 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_11);
lean_ctor_set_uint16(x_14, sizeof(void*)*2 + 4, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 7, x_13);
x_15 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_16 = 0;
x_17 = 0;
x_18 = 0;
x_19 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_uint16(x_19, sizeof(void*)*2 + 4, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 7, x_18);
x_20 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_3);
lean_dec(x_3);
x_21 = 0;
x_22 = 0;
x_23 = 0;
x_24 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_uint16(x_24, sizeof(void*)*2 + 4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 7, x_23);
x_25 = l_Lean_formatEntry___closed__2;
x_26 = 0;
x_27 = 0;
x_28 = 0;
x_29 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_29, sizeof(void*)*2, x_26);
lean_ctor_set_uint16(x_29, sizeof(void*)*2 + 4, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 7, x_28);
x_30 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(x_4);
x_31 = 0;
x_32 = 0;
x_33 = 0;
x_34 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_34, sizeof(void*)*2, x_31);
lean_ctor_set_uint16(x_34, sizeof(void*)*2 + 4, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 7, x_33);
return x_34;
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint32_t x_45; uint16_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; uint16_t x_51; uint8_t x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Nat_repr(x_35);
x_38 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_box(0);
x_43 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_36, x_36, x_41, x_42);
lean_dec(x_36);
x_44 = 0;
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 6, x_44);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_uint16(x_48, sizeof(void*)*2 + 4, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 7, x_47);
x_49 = l_Lean_IR_formatFnBodyHead___closed__4;
x_50 = 0;
x_51 = 0;
x_52 = 0;
x_53 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 6, x_44);
lean_ctor_set_uint32(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_uint16(x_53, sizeof(void*)*2 + 4, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 7, x_52);
return x_53;
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint32_t x_63; uint16_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint32_t x_68; uint16_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint32_t x_74; uint16_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint32_t x_79; uint16_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint32_t x_84; uint16_t x_85; uint8_t x_86; lean_object* x_87; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
lean_dec(x_1);
x_57 = l_Nat_repr(x_54);
x_58 = l_Lean_IR_VarId_HasToString___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = 0;
x_62 = l_Lean_IR_formatFnBodyHead___closed__6;
x_63 = 0;
x_64 = 0;
x_65 = 0;
x_66 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set_uint8(x_66, sizeof(void*)*2 + 6, x_61);
lean_ctor_set_uint32(x_66, sizeof(void*)*2, x_63);
lean_ctor_set_uint16(x_66, sizeof(void*)*2 + 4, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*2 + 7, x_65);
x_67 = l_Lean_Format_sbracket___closed__2;
x_68 = 0;
x_69 = 0;
x_70 = 0;
x_71 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2 + 6, x_61);
lean_ctor_set_uint32(x_71, sizeof(void*)*2, x_68);
lean_ctor_set_uint16(x_71, sizeof(void*)*2 + 4, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*2 + 7, x_70);
x_72 = l_Nat_repr(x_55);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = 0;
x_75 = 0;
x_76 = 0;
x_77 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 6, x_61);
lean_ctor_set_uint32(x_77, sizeof(void*)*2, x_74);
lean_ctor_set_uint16(x_77, sizeof(void*)*2 + 4, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 7, x_76);
x_78 = l_Lean_IR_formatFnBodyHead___closed__8;
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 6, x_61);
lean_ctor_set_uint32(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_uint16(x_82, sizeof(void*)*2 + 4, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 7, x_81);
x_83 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_56);
x_84 = 0;
x_85 = 0;
x_86 = 0;
x_87 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*2 + 6, x_61);
lean_ctor_set_uint32(x_87, sizeof(void*)*2, x_84);
lean_ctor_set_uint16(x_87, sizeof(void*)*2 + 4, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*2 + 7, x_86);
return x_87;
}
case 3:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; uint32_t x_96; uint16_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; uint32_t x_101; uint16_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint32_t x_107; uint16_t x_108; uint8_t x_109; lean_object* x_110; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_dec(x_1);
x_90 = l_Nat_repr(x_88);
x_91 = l_Lean_IR_VarId_HasToString___closed__1;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = 0;
x_95 = l_Lean_IR_formatFnBodyHead___closed__10;
x_96 = 0;
x_97 = 0;
x_98 = 0;
x_99 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_93);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 6, x_94);
lean_ctor_set_uint32(x_99, sizeof(void*)*2, x_96);
lean_ctor_set_uint16(x_99, sizeof(void*)*2 + 4, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 7, x_98);
x_100 = l_Lean_formatEntry___closed__2;
x_101 = 0;
x_102 = 0;
x_103 = 0;
x_104 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 6, x_94);
lean_ctor_set_uint32(x_104, sizeof(void*)*2, x_101);
lean_ctor_set_uint16(x_104, sizeof(void*)*2 + 4, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 7, x_103);
x_105 = l_Nat_repr(x_89);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = 0;
x_108 = 0;
x_109 = 0;
x_110 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2 + 6, x_94);
lean_ctor_set_uint32(x_110, sizeof(void*)*2, x_107);
lean_ctor_set_uint16(x_110, sizeof(void*)*2 + 4, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*2 + 7, x_109);
return x_110;
}
case 4:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint32_t x_120; uint16_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; uint32_t x_125; uint16_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint32_t x_131; uint16_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; uint32_t x_136; uint16_t x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint32_t x_143; uint16_t x_144; uint8_t x_145; lean_object* x_146; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 2);
lean_inc(x_113);
lean_dec(x_1);
x_114 = l_Nat_repr(x_111);
x_115 = l_Lean_IR_VarId_HasToString___closed__1;
x_116 = lean_string_append(x_115, x_114);
lean_dec(x_114);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = 0;
x_119 = l_Lean_IR_formatFnBodyHead___closed__12;
x_120 = 0;
x_121 = 0;
x_122 = 0;
x_123 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_117);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 6, x_118);
lean_ctor_set_uint32(x_123, sizeof(void*)*2, x_120);
lean_ctor_set_uint16(x_123, sizeof(void*)*2 + 4, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 7, x_122);
x_124 = l_Lean_Format_sbracket___closed__2;
x_125 = 0;
x_126 = 0;
x_127 = 0;
x_128 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_124);
lean_ctor_set_uint8(x_128, sizeof(void*)*2 + 6, x_118);
lean_ctor_set_uint32(x_128, sizeof(void*)*2, x_125);
lean_ctor_set_uint16(x_128, sizeof(void*)*2 + 4, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*2 + 7, x_127);
x_129 = l_Nat_repr(x_112);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = 0;
x_132 = 0;
x_133 = 0;
x_134 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set_uint8(x_134, sizeof(void*)*2 + 6, x_118);
lean_ctor_set_uint32(x_134, sizeof(void*)*2, x_131);
lean_ctor_set_uint16(x_134, sizeof(void*)*2 + 4, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*2 + 7, x_133);
x_135 = l_Lean_IR_formatFnBodyHead___closed__8;
x_136 = 0;
x_137 = 0;
x_138 = 0;
x_139 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set_uint8(x_139, sizeof(void*)*2 + 6, x_118);
lean_ctor_set_uint32(x_139, sizeof(void*)*2, x_136);
lean_ctor_set_uint16(x_139, sizeof(void*)*2 + 4, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*2 + 7, x_138);
x_140 = l_Nat_repr(x_113);
x_141 = lean_string_append(x_115, x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = 0;
x_144 = 0;
x_145 = 0;
x_146 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2 + 6, x_118);
lean_ctor_set_uint32(x_146, sizeof(void*)*2, x_143);
lean_ctor_set_uint16(x_146, sizeof(void*)*2 + 4, x_144);
lean_ctor_set_uint8(x_146, sizeof(void*)*2 + 7, x_145);
return x_146;
}
case 5:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; uint32_t x_158; uint16_t x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; uint32_t x_163; uint16_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint32_t x_169; uint16_t x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; uint32_t x_174; uint16_t x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint32_t x_180; uint16_t x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; uint32_t x_185; uint16_t x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; uint32_t x_190; uint16_t x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; uint32_t x_195; uint16_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint32_t x_202; uint16_t x_203; uint8_t x_204; lean_object* x_205; 
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_1, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_1, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_1, 4);
lean_inc(x_151);
lean_dec(x_1);
x_152 = l_Nat_repr(x_147);
x_153 = l_Lean_IR_VarId_HasToString___closed__1;
x_154 = lean_string_append(x_153, x_152);
lean_dec(x_152);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = 0;
x_157 = l_Lean_IR_formatFnBodyHead___closed__14;
x_158 = 0;
x_159 = 0;
x_160 = 0;
x_161 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set_uint8(x_161, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_161, sizeof(void*)*2, x_158);
lean_ctor_set_uint16(x_161, sizeof(void*)*2 + 4, x_159);
lean_ctor_set_uint8(x_161, sizeof(void*)*2 + 7, x_160);
x_162 = l_Lean_Format_sbracket___closed__2;
x_163 = 0;
x_164 = 0;
x_165 = 0;
x_166 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_162);
lean_ctor_set_uint8(x_166, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_166, sizeof(void*)*2, x_163);
lean_ctor_set_uint16(x_166, sizeof(void*)*2 + 4, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*2 + 7, x_165);
x_167 = l_Nat_repr(x_148);
x_168 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = 0;
x_170 = 0;
x_171 = 0;
x_172 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_168);
lean_ctor_set_uint8(x_172, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_172, sizeof(void*)*2, x_169);
lean_ctor_set_uint16(x_172, sizeof(void*)*2 + 4, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*2 + 7, x_171);
x_173 = l_Lean_formatKVMap___closed__1;
x_174 = 0;
x_175 = 0;
x_176 = 0;
x_177 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_173);
lean_ctor_set_uint8(x_177, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_177, sizeof(void*)*2, x_174);
lean_ctor_set_uint16(x_177, sizeof(void*)*2 + 4, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*2 + 7, x_176);
x_178 = l_Nat_repr(x_149);
x_179 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = 0;
x_181 = 0;
x_182 = 0;
x_183 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_179);
lean_ctor_set_uint8(x_183, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_183, sizeof(void*)*2, x_180);
lean_ctor_set_uint16(x_183, sizeof(void*)*2 + 4, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*2 + 7, x_182);
x_184 = l_Lean_IR_formatFnBodyHead___closed__16;
x_185 = 0;
x_186 = 0;
x_187 = 0;
x_188 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set_uint8(x_188, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_188, sizeof(void*)*2, x_185);
lean_ctor_set_uint16(x_188, sizeof(void*)*2 + 4, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*2 + 7, x_187);
x_189 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_151);
lean_dec(x_151);
x_190 = 0;
x_191 = 0;
x_192 = 0;
x_193 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set_uint8(x_193, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_193, sizeof(void*)*2, x_190);
lean_ctor_set_uint16(x_193, sizeof(void*)*2 + 4, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*2 + 7, x_192);
x_194 = l_Lean_formatEntry___closed__2;
x_195 = 0;
x_196 = 0;
x_197 = 0;
x_198 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_198, sizeof(void*)*2, x_195);
lean_ctor_set_uint16(x_198, sizeof(void*)*2 + 4, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 7, x_197);
x_199 = l_Nat_repr(x_150);
x_200 = lean_string_append(x_153, x_199);
lean_dec(x_199);
x_201 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = 0;
x_203 = 0;
x_204 = 0;
x_205 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_201);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 6, x_156);
lean_ctor_set_uint32(x_205, sizeof(void*)*2, x_202);
lean_ctor_set_uint16(x_205, sizeof(void*)*2 + 4, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 7, x_204);
return x_205;
}
case 6:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_206 = lean_ctor_get(x_1, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_1, 1);
lean_inc(x_207);
lean_dec(x_1);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_dec_eq(x_207, x_208);
x_210 = l_Nat_repr(x_206);
x_211 = l_Lean_IR_VarId_HasToString___closed__1;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_212);
if (x_209 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint32_t x_218; uint16_t x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint32_t x_231; uint16_t x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; uint32_t x_236; uint16_t x_237; uint8_t x_238; lean_object* x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; 
x_214 = l_Nat_repr(x_207);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = 0;
x_217 = l_Lean_Format_sbracket___closed__2;
x_218 = 0;
x_219 = 0;
x_220 = 0;
x_221 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_221, 0, x_217);
lean_ctor_set(x_221, 1, x_215);
lean_ctor_set_uint8(x_221, sizeof(void*)*2 + 6, x_216);
lean_ctor_set_uint32(x_221, sizeof(void*)*2, x_218);
lean_ctor_set_uint16(x_221, sizeof(void*)*2 + 4, x_219);
lean_ctor_set_uint8(x_221, sizeof(void*)*2 + 7, x_220);
x_222 = l_Lean_Format_sbracket___closed__3;
x_223 = 0;
x_224 = 0;
x_225 = 0;
x_226 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set_uint8(x_226, sizeof(void*)*2 + 6, x_216);
lean_ctor_set_uint32(x_226, sizeof(void*)*2, x_223);
lean_ctor_set_uint16(x_226, sizeof(void*)*2 + 4, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*2 + 7, x_225);
x_227 = l_Lean_Format_sbracket___closed__1;
x_228 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_format_group(x_228);
x_230 = l_Lean_IR_formatFnBodyHead___closed__18;
x_231 = 0;
x_232 = 0;
x_233 = 0;
x_234 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_229);
lean_ctor_set_uint8(x_234, sizeof(void*)*2 + 6, x_216);
lean_ctor_set_uint32(x_234, sizeof(void*)*2, x_231);
lean_ctor_set_uint16(x_234, sizeof(void*)*2 + 4, x_232);
lean_ctor_set_uint8(x_234, sizeof(void*)*2 + 7, x_233);
x_235 = l_Lean_Format_flatten___main___closed__1;
x_236 = 0;
x_237 = 0;
x_238 = 0;
x_239 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_239, 0, x_234);
lean_ctor_set(x_239, 1, x_235);
lean_ctor_set_uint8(x_239, sizeof(void*)*2 + 6, x_216);
lean_ctor_set_uint32(x_239, sizeof(void*)*2, x_236);
lean_ctor_set_uint16(x_239, sizeof(void*)*2 + 4, x_237);
lean_ctor_set_uint8(x_239, sizeof(void*)*2 + 7, x_238);
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_243, 0, x_239);
lean_ctor_set(x_243, 1, x_213);
lean_ctor_set_uint8(x_243, sizeof(void*)*2 + 6, x_216);
lean_ctor_set_uint32(x_243, sizeof(void*)*2, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*2 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*2 + 7, x_242);
return x_243;
}
else
{
uint8_t x_244; lean_object* x_245; uint32_t x_246; uint16_t x_247; uint8_t x_248; lean_object* x_249; 
lean_dec(x_207);
x_244 = 0;
x_245 = l_Lean_IR_formatFnBodyHead___closed__20;
x_246 = 0;
x_247 = 0;
x_248 = 0;
x_249 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_249, 0, x_245);
lean_ctor_set(x_249, 1, x_213);
lean_ctor_set_uint8(x_249, sizeof(void*)*2 + 6, x_244);
lean_ctor_set_uint32(x_249, sizeof(void*)*2, x_246);
lean_ctor_set_uint16(x_249, sizeof(void*)*2 + 4, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*2 + 7, x_248);
return x_249;
}
}
case 7:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_250 = lean_ctor_get(x_1, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_1, 1);
lean_inc(x_251);
lean_dec(x_1);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_dec_eq(x_251, x_252);
x_254 = l_Nat_repr(x_250);
x_255 = l_Lean_IR_VarId_HasToString___closed__1;
x_256 = lean_string_append(x_255, x_254);
lean_dec(x_254);
x_257 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_257, 0, x_256);
if (x_253 == 0)
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; uint32_t x_262; uint16_t x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; uint32_t x_267; uint16_t x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint32_t x_275; uint16_t x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; uint32_t x_280; uint16_t x_281; uint8_t x_282; lean_object* x_283; uint32_t x_284; uint16_t x_285; uint8_t x_286; lean_object* x_287; 
x_258 = l_Nat_repr(x_251);
x_259 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = 0;
x_261 = l_Lean_Format_sbracket___closed__2;
x_262 = 0;
x_263 = 0;
x_264 = 0;
x_265 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_259);
lean_ctor_set_uint8(x_265, sizeof(void*)*2 + 6, x_260);
lean_ctor_set_uint32(x_265, sizeof(void*)*2, x_262);
lean_ctor_set_uint16(x_265, sizeof(void*)*2 + 4, x_263);
lean_ctor_set_uint8(x_265, sizeof(void*)*2 + 7, x_264);
x_266 = l_Lean_Format_sbracket___closed__3;
x_267 = 0;
x_268 = 0;
x_269 = 0;
x_270 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_270, 0, x_265);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set_uint8(x_270, sizeof(void*)*2 + 6, x_260);
lean_ctor_set_uint32(x_270, sizeof(void*)*2, x_267);
lean_ctor_set_uint16(x_270, sizeof(void*)*2 + 4, x_268);
lean_ctor_set_uint8(x_270, sizeof(void*)*2 + 7, x_269);
x_271 = l_Lean_Format_sbracket___closed__1;
x_272 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_273 = lean_format_group(x_272);
x_274 = l_Lean_IR_formatFnBodyHead___closed__22;
x_275 = 0;
x_276 = 0;
x_277 = 0;
x_278 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_278, 0, x_274);
lean_ctor_set(x_278, 1, x_273);
lean_ctor_set_uint8(x_278, sizeof(void*)*2 + 6, x_260);
lean_ctor_set_uint32(x_278, sizeof(void*)*2, x_275);
lean_ctor_set_uint16(x_278, sizeof(void*)*2 + 4, x_276);
lean_ctor_set_uint8(x_278, sizeof(void*)*2 + 7, x_277);
x_279 = l_Lean_Format_flatten___main___closed__1;
x_280 = 0;
x_281 = 0;
x_282 = 0;
x_283 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_283, 0, x_278);
lean_ctor_set(x_283, 1, x_279);
lean_ctor_set_uint8(x_283, sizeof(void*)*2 + 6, x_260);
lean_ctor_set_uint32(x_283, sizeof(void*)*2, x_280);
lean_ctor_set_uint16(x_283, sizeof(void*)*2 + 4, x_281);
lean_ctor_set_uint8(x_283, sizeof(void*)*2 + 7, x_282);
x_284 = 0;
x_285 = 0;
x_286 = 0;
x_287 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_287, 0, x_283);
lean_ctor_set(x_287, 1, x_257);
lean_ctor_set_uint8(x_287, sizeof(void*)*2 + 6, x_260);
lean_ctor_set_uint32(x_287, sizeof(void*)*2, x_284);
lean_ctor_set_uint16(x_287, sizeof(void*)*2 + 4, x_285);
lean_ctor_set_uint8(x_287, sizeof(void*)*2 + 7, x_286);
return x_287;
}
else
{
uint8_t x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; lean_object* x_293; 
lean_dec(x_251);
x_288 = 0;
x_289 = l_Lean_IR_formatFnBodyHead___closed__24;
x_290 = 0;
x_291 = 0;
x_292 = 0;
x_293 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_293, 0, x_289);
lean_ctor_set(x_293, 1, x_257);
lean_ctor_set_uint8(x_293, sizeof(void*)*2 + 6, x_288);
lean_ctor_set_uint32(x_293, sizeof(void*)*2, x_290);
lean_ctor_set_uint16(x_293, sizeof(void*)*2 + 4, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*2 + 7, x_292);
return x_293;
}
}
case 8:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; uint32_t x_301; uint16_t x_302; uint8_t x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_1, 0);
lean_inc(x_294);
lean_dec(x_1);
x_295 = l_Nat_repr(x_294);
x_296 = l_Lean_IR_VarId_HasToString___closed__1;
x_297 = lean_string_append(x_296, x_295);
lean_dec(x_295);
x_298 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = 0;
x_300 = l_Lean_IR_formatFnBodyHead___closed__26;
x_301 = 0;
x_302 = 0;
x_303 = 0;
x_304 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_298);
lean_ctor_set_uint8(x_304, sizeof(void*)*2 + 6, x_299);
lean_ctor_set_uint32(x_304, sizeof(void*)*2, x_301);
lean_ctor_set_uint16(x_304, sizeof(void*)*2 + 4, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*2 + 7, x_303);
return x_304;
}
case 9:
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; uint32_t x_309; uint16_t x_310; uint8_t x_311; lean_object* x_312; 
x_305 = lean_ctor_get(x_1, 0);
lean_inc(x_305);
lean_dec(x_1);
x_306 = l_Lean_formatKVMap(x_305);
x_307 = 0;
x_308 = l_Lean_IR_formatFnBodyHead___closed__28;
x_309 = 0;
x_310 = 0;
x_311 = 0;
x_312 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_312, 0, x_308);
lean_ctor_set(x_312, 1, x_306);
lean_ctor_set_uint8(x_312, sizeof(void*)*2 + 6, x_307);
lean_ctor_set_uint32(x_312, sizeof(void*)*2, x_309);
lean_ctor_set_uint16(x_312, sizeof(void*)*2 + 4, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*2 + 7, x_311);
return x_312;
}
case 10:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; uint32_t x_320; uint16_t x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; uint32_t x_325; uint16_t x_326; uint8_t x_327; lean_object* x_328; 
x_313 = lean_ctor_get(x_1, 1);
lean_inc(x_313);
lean_dec(x_1);
x_314 = l_Nat_repr(x_313);
x_315 = l_Lean_IR_VarId_HasToString___closed__1;
x_316 = lean_string_append(x_315, x_314);
lean_dec(x_314);
x_317 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = 0;
x_319 = l_Lean_IR_formatFnBodyHead___closed__30;
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set_uint8(x_323, sizeof(void*)*2 + 6, x_318);
lean_ctor_set_uint32(x_323, sizeof(void*)*2, x_320);
lean_ctor_set_uint16(x_323, sizeof(void*)*2 + 4, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*2 + 7, x_322);
x_324 = l_Lean_IR_formatFnBodyHead___closed__32;
x_325 = 0;
x_326 = 0;
x_327 = 0;
x_328 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_328, 0, x_323);
lean_ctor_set(x_328, 1, x_324);
lean_ctor_set_uint8(x_328, sizeof(void*)*2 + 6, x_318);
lean_ctor_set_uint32(x_328, sizeof(void*)*2, x_325);
lean_ctor_set_uint16(x_328, sizeof(void*)*2 + 4, x_326);
lean_ctor_set_uint8(x_328, sizeof(void*)*2 + 7, x_327);
return x_328;
}
case 11:
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint32_t x_333; uint16_t x_334; uint8_t x_335; lean_object* x_336; 
x_329 = lean_ctor_get(x_1, 0);
lean_inc(x_329);
lean_dec(x_1);
x_330 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_329);
x_331 = 0;
x_332 = l_Lean_IR_formatFnBodyHead___closed__34;
x_333 = 0;
x_334 = 0;
x_335 = 0;
x_336 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_336, 0, x_332);
lean_ctor_set(x_336, 1, x_330);
lean_ctor_set_uint8(x_336, sizeof(void*)*2 + 6, x_331);
lean_ctor_set_uint32(x_336, sizeof(void*)*2, x_333);
lean_ctor_set_uint16(x_336, sizeof(void*)*2 + 4, x_334);
lean_ctor_set_uint8(x_336, sizeof(void*)*2 + 7, x_335);
return x_336;
}
case 12:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; uint32_t x_345; uint16_t x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint32_t x_352; uint16_t x_353; uint8_t x_354; lean_object* x_355; 
x_337 = lean_ctor_get(x_1, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_1, 1);
lean_inc(x_338);
lean_dec(x_1);
x_339 = l_Nat_repr(x_337);
x_340 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_341 = lean_string_append(x_340, x_339);
lean_dec(x_339);
x_342 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_342, 0, x_341);
x_343 = 0;
x_344 = l_Lean_IR_formatFnBodyHead___closed__36;
x_345 = 0;
x_346 = 0;
x_347 = 0;
x_348 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_342);
lean_ctor_set_uint8(x_348, sizeof(void*)*2 + 6, x_343);
lean_ctor_set_uint32(x_348, sizeof(void*)*2, x_345);
lean_ctor_set_uint16(x_348, sizeof(void*)*2 + 4, x_346);
lean_ctor_set_uint8(x_348, sizeof(void*)*2 + 7, x_347);
x_349 = lean_unsigned_to_nat(0u);
x_350 = lean_box(0);
x_351 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_338, x_338, x_349, x_350);
lean_dec(x_338);
x_352 = 0;
x_353 = 0;
x_354 = 0;
x_355 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_355, 0, x_348);
lean_ctor_set(x_355, 1, x_351);
lean_ctor_set_uint8(x_355, sizeof(void*)*2 + 6, x_343);
lean_ctor_set_uint32(x_355, sizeof(void*)*2, x_352);
lean_ctor_set_uint16(x_355, sizeof(void*)*2 + 4, x_353);
lean_ctor_set_uint8(x_355, sizeof(void*)*2 + 7, x_354);
return x_355;
}
default: 
{
lean_object* x_356; 
x_356 = l_Lean_IR_formatFnBodyHead___closed__38;
return x_356;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint32_t x_11; uint16_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; uint16_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
x_10 = lean_box(1);
x_11 = 0;
x_12 = 0;
x_13 = 0;
x_14 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_11);
lean_ctor_set_uint16(x_14, sizeof(void*)*2 + 4, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 7, x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_IR_formatFnBody___main), 2, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_1);
x_16 = l_Lean_IR_formatAlt(x_15, x_1, x_8);
x_17 = 0;
x_18 = 0;
x_19 = 0;
x_20 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 6, x_9);
lean_ctor_set_uint32(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_uint16(x_20, sizeof(void*)*2 + 4, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 7, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_4 = x_22;
x_5 = x_20;
goto _start;
}
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBody___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :=");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBody___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" of");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBody___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint32_t x_13; uint16_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; uint16_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint16_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; uint16_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; uint16_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; uint16_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint16_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; uint16_t x_49; uint8_t x_50; lean_object* x_51; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Nat_repr(x_3);
x_8 = l_Lean_IR_VarId_HasToString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l_Lean_IR_formatFnBodyHead___closed__2;
x_13 = 0;
x_14 = 0;
x_15 = 0;
x_16 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_16, sizeof(void*)*2, x_13);
lean_ctor_set_uint16(x_16, sizeof(void*)*2 + 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 7, x_15);
x_17 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_18 = 0;
x_19 = 0;
x_20 = 0;
x_21 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_21, sizeof(void*)*2, x_18);
lean_ctor_set_uint16(x_21, sizeof(void*)*2 + 4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 7, x_20);
x_22 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_4);
lean_dec(x_4);
x_23 = 0;
x_24 = 0;
x_25 = 0;
x_26 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_uint16(x_26, sizeof(void*)*2 + 4, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 7, x_25);
x_27 = l_Lean_formatEntry___closed__2;
x_28 = 0;
x_29 = 0;
x_30 = 0;
x_31 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_uint16(x_31, sizeof(void*)*2 + 4, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 7, x_30);
x_32 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(x_5);
x_33 = 0;
x_34 = 0;
x_35 = 0;
x_36 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_36, sizeof(void*)*2, x_33);
lean_ctor_set_uint16(x_36, sizeof(void*)*2 + 4, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*2 + 7, x_35);
x_37 = l_Lean_IR_formatFnBody___main___closed__2;
x_38 = 0;
x_39 = 0;
x_40 = 0;
x_41 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_uint16(x_41, sizeof(void*)*2 + 4, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 7, x_40);
x_42 = lean_box(1);
x_43 = 0;
x_44 = 0;
x_45 = 0;
x_46 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_uint16(x_46, sizeof(void*)*2 + 4, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 7, x_45);
x_47 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_48 = 0;
x_49 = 0;
x_50 = 0;
x_51 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint32(x_51, sizeof(void*)*2, x_48);
lean_ctor_set_uint16(x_51, sizeof(void*)*2 + 4, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 7, x_50);
return x_51;
}
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; uint16_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint32_t x_75; uint16_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint32_t x_85; uint16_t x_86; uint8_t x_87; lean_object* x_88; uint32_t x_89; uint16_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint32_t x_94; uint16_t x_95; uint8_t x_96; lean_object* x_97; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 3);
lean_inc(x_55);
lean_dec(x_2);
x_56 = l_Nat_repr(x_52);
x_57 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_box(0);
x_62 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_53, x_53, x_60, x_61);
lean_dec(x_53);
x_63 = 0;
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_uint16(x_67, sizeof(void*)*2 + 4, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 7, x_66);
x_68 = l_Lean_IR_formatFnBody___main___closed__4;
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_uint16(x_72, sizeof(void*)*2 + 4, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 7, x_71);
lean_inc(x_1);
x_73 = l_Lean_IR_formatFnBody___main(x_1, x_54);
x_74 = lean_box(1);
x_75 = 0;
x_76 = 0;
x_77 = 0;
x_78 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_78, sizeof(void*)*2, x_75);
lean_ctor_set_uint16(x_78, sizeof(void*)*2 + 4, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 7, x_77);
lean_inc(x_1);
x_79 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
x_80 = 0;
x_81 = 0;
x_82 = 0;
x_83 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_83, sizeof(void*)*2, x_80);
lean_ctor_set_uint16(x_83, sizeof(void*)*2 + 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*2 + 7, x_82);
x_84 = l_Lean_IR_formatFnBody___main___closed__2;
x_85 = 0;
x_86 = 0;
x_87 = 0;
x_88 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_88, sizeof(void*)*2, x_85);
lean_ctor_set_uint16(x_88, sizeof(void*)*2 + 4, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 7, x_87);
x_89 = 0;
x_90 = 0;
x_91 = 0;
x_92 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_74);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_uint16(x_92, sizeof(void*)*2 + 4, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 7, x_91);
x_93 = l_Lean_IR_formatFnBody___main(x_1, x_55);
x_94 = 0;
x_95 = 0;
x_96 = 0;
x_97 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_93);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 6, x_63);
lean_ctor_set_uint32(x_97, sizeof(void*)*2, x_94);
lean_ctor_set_uint16(x_97, sizeof(void*)*2 + 4, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 7, x_96);
return x_97;
}
case 2:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint32_t x_108; uint16_t x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint32_t x_119; uint16_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; uint32_t x_124; uint16_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint32_t x_129; uint16_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; uint32_t x_134; uint16_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint32_t x_139; uint16_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint32_t x_144; uint16_t x_145; uint8_t x_146; lean_object* x_147; 
x_98 = lean_ctor_get(x_2, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 3);
lean_inc(x_101);
lean_dec(x_2);
x_102 = l_Nat_repr(x_98);
x_103 = l_Lean_IR_VarId_HasToString___closed__1;
x_104 = lean_string_append(x_103, x_102);
lean_dec(x_102);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = 0;
x_107 = l_Lean_IR_formatFnBodyHead___closed__6;
x_108 = 0;
x_109 = 0;
x_110 = 0;
x_111 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set_uint8(x_111, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_111, sizeof(void*)*2, x_108);
lean_ctor_set_uint16(x_111, sizeof(void*)*2 + 4, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*2 + 7, x_110);
x_112 = l_Lean_Format_sbracket___closed__2;
x_113 = 0;
x_114 = 0;
x_115 = 0;
x_116 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_116, sizeof(void*)*2, x_113);
lean_ctor_set_uint16(x_116, sizeof(void*)*2 + 4, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 7, x_115);
x_117 = l_Nat_repr(x_99);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = 0;
x_120 = 0;
x_121 = 0;
x_122 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_122, sizeof(void*)*2, x_119);
lean_ctor_set_uint16(x_122, sizeof(void*)*2 + 4, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 7, x_121);
x_123 = l_Lean_IR_formatFnBodyHead___closed__8;
x_124 = 0;
x_125 = 0;
x_126 = 0;
x_127 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set_uint8(x_127, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_127, sizeof(void*)*2, x_124);
lean_ctor_set_uint16(x_127, sizeof(void*)*2 + 4, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*2 + 7, x_126);
x_128 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_100);
x_129 = 0;
x_130 = 0;
x_131 = 0;
x_132 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_132, sizeof(void*)*2, x_129);
lean_ctor_set_uint16(x_132, sizeof(void*)*2 + 4, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*2 + 7, x_131);
x_133 = l_Lean_IR_formatFnBody___main___closed__2;
x_134 = 0;
x_135 = 0;
x_136 = 0;
x_137 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set_uint8(x_137, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_137, sizeof(void*)*2, x_134);
lean_ctor_set_uint16(x_137, sizeof(void*)*2 + 4, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*2 + 7, x_136);
x_138 = lean_box(1);
x_139 = 0;
x_140 = 0;
x_141 = 0;
x_142 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_138);
lean_ctor_set_uint8(x_142, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_142, sizeof(void*)*2, x_139);
lean_ctor_set_uint16(x_142, sizeof(void*)*2 + 4, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*2 + 7, x_141);
x_143 = l_Lean_IR_formatFnBody___main(x_1, x_101);
x_144 = 0;
x_145 = 0;
x_146 = 0;
x_147 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set_uint8(x_147, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint32(x_147, sizeof(void*)*2, x_144);
lean_ctor_set_uint16(x_147, sizeof(void*)*2 + 4, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*2 + 7, x_146);
return x_147;
}
case 3:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; uint32_t x_157; uint16_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; uint32_t x_162; uint16_t x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint32_t x_168; uint16_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; uint32_t x_173; uint16_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; uint32_t x_178; uint16_t x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; uint32_t x_183; uint16_t x_184; uint8_t x_185; lean_object* x_186; 
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 2);
lean_inc(x_150);
lean_dec(x_2);
x_151 = l_Nat_repr(x_148);
x_152 = l_Lean_IR_VarId_HasToString___closed__1;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = 0;
x_156 = l_Lean_IR_formatFnBodyHead___closed__10;
x_157 = 0;
x_158 = 0;
x_159 = 0;
x_160 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 6, x_155);
lean_ctor_set_uint32(x_160, sizeof(void*)*2, x_157);
lean_ctor_set_uint16(x_160, sizeof(void*)*2 + 4, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 7, x_159);
x_161 = l_Lean_formatEntry___closed__2;
x_162 = 0;
x_163 = 0;
x_164 = 0;
x_165 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set_uint8(x_165, sizeof(void*)*2 + 6, x_155);
lean_ctor_set_uint32(x_165, sizeof(void*)*2, x_162);
lean_ctor_set_uint16(x_165, sizeof(void*)*2 + 4, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*2 + 7, x_164);
x_166 = l_Nat_repr(x_149);
x_167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = 0;
x_169 = 0;
x_170 = 0;
x_171 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*2 + 6, x_155);
lean_ctor_set_uint32(x_171, sizeof(void*)*2, x_168);
lean_ctor_set_uint16(x_171, sizeof(void*)*2 + 4, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*2 + 7, x_170);
x_172 = l_Lean_IR_formatFnBody___main___closed__2;
x_173 = 0;
x_174 = 0;
x_175 = 0;
x_176 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_172);
lean_ctor_set_uint8(x_176, sizeof(void*)*2 + 6, x_155);
lean_ctor_set_uint32(x_176, sizeof(void*)*2, x_173);
lean_ctor_set_uint16(x_176, sizeof(void*)*2 + 4, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*2 + 7, x_175);
x_177 = lean_box(1);
x_178 = 0;
x_179 = 0;
x_180 = 0;
x_181 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set_uint8(x_181, sizeof(void*)*2 + 6, x_155);
lean_ctor_set_uint32(x_181, sizeof(void*)*2, x_178);
lean_ctor_set_uint16(x_181, sizeof(void*)*2 + 4, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*2 + 7, x_180);
x_182 = l_Lean_IR_formatFnBody___main(x_1, x_150);
x_183 = 0;
x_184 = 0;
x_185 = 0;
x_186 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set_uint8(x_186, sizeof(void*)*2 + 6, x_155);
lean_ctor_set_uint32(x_186, sizeof(void*)*2, x_183);
lean_ctor_set_uint16(x_186, sizeof(void*)*2 + 4, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*2 + 7, x_185);
return x_186;
}
case 4:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; uint32_t x_197; uint16_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; uint32_t x_202; uint16_t x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint32_t x_208; uint16_t x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; uint32_t x_213; uint16_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint32_t x_220; uint16_t x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; uint32_t x_225; uint16_t x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; uint32_t x_230; uint16_t x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; uint32_t x_235; uint16_t x_236; uint8_t x_237; lean_object* x_238; 
x_187 = lean_ctor_get(x_2, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_2, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_2, 3);
lean_inc(x_190);
lean_dec(x_2);
x_191 = l_Nat_repr(x_187);
x_192 = l_Lean_IR_VarId_HasToString___closed__1;
x_193 = lean_string_append(x_192, x_191);
lean_dec(x_191);
x_194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = 0;
x_196 = l_Lean_IR_formatFnBodyHead___closed__12;
x_197 = 0;
x_198 = 0;
x_199 = 0;
x_200 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set(x_200, 1, x_194);
lean_ctor_set_uint8(x_200, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_200, sizeof(void*)*2, x_197);
lean_ctor_set_uint16(x_200, sizeof(void*)*2 + 4, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*2 + 7, x_199);
x_201 = l_Lean_Format_sbracket___closed__2;
x_202 = 0;
x_203 = 0;
x_204 = 0;
x_205 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_205, 0, x_200);
lean_ctor_set(x_205, 1, x_201);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_205, sizeof(void*)*2, x_202);
lean_ctor_set_uint16(x_205, sizeof(void*)*2 + 4, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 7, x_204);
x_206 = l_Nat_repr(x_188);
x_207 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = 0;
x_209 = 0;
x_210 = 0;
x_211 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_207);
lean_ctor_set_uint8(x_211, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_211, sizeof(void*)*2, x_208);
lean_ctor_set_uint16(x_211, sizeof(void*)*2 + 4, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*2 + 7, x_210);
x_212 = l_Lean_IR_formatFnBodyHead___closed__8;
x_213 = 0;
x_214 = 0;
x_215 = 0;
x_216 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_212);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_216, sizeof(void*)*2, x_213);
lean_ctor_set_uint16(x_216, sizeof(void*)*2 + 4, x_214);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 7, x_215);
x_217 = l_Nat_repr(x_189);
x_218 = lean_string_append(x_192, x_217);
lean_dec(x_217);
x_219 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = 0;
x_221 = 0;
x_222 = 0;
x_223 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_223, 0, x_216);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set_uint8(x_223, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_223, sizeof(void*)*2, x_220);
lean_ctor_set_uint16(x_223, sizeof(void*)*2 + 4, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*2 + 7, x_222);
x_224 = l_Lean_IR_formatFnBody___main___closed__2;
x_225 = 0;
x_226 = 0;
x_227 = 0;
x_228 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_228, 0, x_223);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set_uint8(x_228, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_228, sizeof(void*)*2, x_225);
lean_ctor_set_uint16(x_228, sizeof(void*)*2 + 4, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*2 + 7, x_227);
x_229 = lean_box(1);
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_233, 0, x_228);
lean_ctor_set(x_233, 1, x_229);
lean_ctor_set_uint8(x_233, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_233, sizeof(void*)*2, x_230);
lean_ctor_set_uint16(x_233, sizeof(void*)*2 + 4, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*2 + 7, x_232);
x_234 = l_Lean_IR_formatFnBody___main(x_1, x_190);
x_235 = 0;
x_236 = 0;
x_237 = 0;
x_238 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 6, x_195);
lean_ctor_set_uint32(x_238, sizeof(void*)*2, x_235);
lean_ctor_set_uint16(x_238, sizeof(void*)*2 + 4, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 7, x_237);
return x_238;
}
case 5:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; uint32_t x_251; uint16_t x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; uint32_t x_256; uint16_t x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint32_t x_262; uint16_t x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; uint32_t x_267; uint16_t x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint32_t x_273; uint16_t x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; uint32_t x_278; uint16_t x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; uint32_t x_283; uint16_t x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; uint32_t x_288; uint16_t x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint32_t x_295; uint16_t x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; uint32_t x_300; uint16_t x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint32_t x_305; uint16_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; uint32_t x_310; uint16_t x_311; uint8_t x_312; lean_object* x_313; 
x_239 = lean_ctor_get(x_2, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_2, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_2, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_2, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_2, 4);
lean_inc(x_243);
x_244 = lean_ctor_get(x_2, 5);
lean_inc(x_244);
lean_dec(x_2);
x_245 = l_Nat_repr(x_239);
x_246 = l_Lean_IR_VarId_HasToString___closed__1;
x_247 = lean_string_append(x_246, x_245);
lean_dec(x_245);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = 0;
x_250 = l_Lean_IR_formatFnBodyHead___closed__14;
x_251 = 0;
x_252 = 0;
x_253 = 0;
x_254 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_254, 0, x_250);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set_uint8(x_254, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_254, sizeof(void*)*2, x_251);
lean_ctor_set_uint16(x_254, sizeof(void*)*2 + 4, x_252);
lean_ctor_set_uint8(x_254, sizeof(void*)*2 + 7, x_253);
x_255 = l_Lean_Format_sbracket___closed__2;
x_256 = 0;
x_257 = 0;
x_258 = 0;
x_259 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_259, 0, x_254);
lean_ctor_set(x_259, 1, x_255);
lean_ctor_set_uint8(x_259, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_259, sizeof(void*)*2, x_256);
lean_ctor_set_uint16(x_259, sizeof(void*)*2 + 4, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*2 + 7, x_258);
x_260 = l_Nat_repr(x_240);
x_261 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = 0;
x_263 = 0;
x_264 = 0;
x_265 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_265, 0, x_259);
lean_ctor_set(x_265, 1, x_261);
lean_ctor_set_uint8(x_265, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_265, sizeof(void*)*2, x_262);
lean_ctor_set_uint16(x_265, sizeof(void*)*2 + 4, x_263);
lean_ctor_set_uint8(x_265, sizeof(void*)*2 + 7, x_264);
x_266 = l_Lean_formatKVMap___closed__1;
x_267 = 0;
x_268 = 0;
x_269 = 0;
x_270 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_270, 0, x_265);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set_uint8(x_270, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_270, sizeof(void*)*2, x_267);
lean_ctor_set_uint16(x_270, sizeof(void*)*2 + 4, x_268);
lean_ctor_set_uint8(x_270, sizeof(void*)*2 + 7, x_269);
x_271 = l_Nat_repr(x_241);
x_272 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_273 = 0;
x_274 = 0;
x_275 = 0;
x_276 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_276, 0, x_270);
lean_ctor_set(x_276, 1, x_272);
lean_ctor_set_uint8(x_276, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_276, sizeof(void*)*2, x_273);
lean_ctor_set_uint16(x_276, sizeof(void*)*2 + 4, x_274);
lean_ctor_set_uint8(x_276, sizeof(void*)*2 + 7, x_275);
x_277 = l_Lean_IR_formatFnBodyHead___closed__16;
x_278 = 0;
x_279 = 0;
x_280 = 0;
x_281 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_277);
lean_ctor_set_uint8(x_281, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_281, sizeof(void*)*2, x_278);
lean_ctor_set_uint16(x_281, sizeof(void*)*2 + 4, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*2 + 7, x_280);
x_282 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_243);
lean_dec(x_243);
x_283 = 0;
x_284 = 0;
x_285 = 0;
x_286 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_282);
lean_ctor_set_uint8(x_286, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_286, sizeof(void*)*2, x_283);
lean_ctor_set_uint16(x_286, sizeof(void*)*2 + 4, x_284);
lean_ctor_set_uint8(x_286, sizeof(void*)*2 + 7, x_285);
x_287 = l_Lean_formatEntry___closed__2;
x_288 = 0;
x_289 = 0;
x_290 = 0;
x_291 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_287);
lean_ctor_set_uint8(x_291, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_291, sizeof(void*)*2, x_288);
lean_ctor_set_uint16(x_291, sizeof(void*)*2 + 4, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*2 + 7, x_290);
x_292 = l_Nat_repr(x_242);
x_293 = lean_string_append(x_246, x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_295 = 0;
x_296 = 0;
x_297 = 0;
x_298 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_298, 0, x_291);
lean_ctor_set(x_298, 1, x_294);
lean_ctor_set_uint8(x_298, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_298, sizeof(void*)*2, x_295);
lean_ctor_set_uint16(x_298, sizeof(void*)*2 + 4, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*2 + 7, x_297);
x_299 = l_Lean_IR_formatFnBody___main___closed__2;
x_300 = 0;
x_301 = 0;
x_302 = 0;
x_303 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_303, 0, x_298);
lean_ctor_set(x_303, 1, x_299);
lean_ctor_set_uint8(x_303, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_303, sizeof(void*)*2, x_300);
lean_ctor_set_uint16(x_303, sizeof(void*)*2 + 4, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*2 + 7, x_302);
x_304 = lean_box(1);
x_305 = 0;
x_306 = 0;
x_307 = 0;
x_308 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_308, 0, x_303);
lean_ctor_set(x_308, 1, x_304);
lean_ctor_set_uint8(x_308, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_308, sizeof(void*)*2, x_305);
lean_ctor_set_uint16(x_308, sizeof(void*)*2 + 4, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*2 + 7, x_307);
x_309 = l_Lean_IR_formatFnBody___main(x_1, x_244);
x_310 = 0;
x_311 = 0;
x_312 = 0;
x_313 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_313, 0, x_308);
lean_ctor_set(x_313, 1, x_309);
lean_ctor_set_uint8(x_313, sizeof(void*)*2 + 6, x_249);
lean_ctor_set_uint32(x_313, sizeof(void*)*2, x_310);
lean_ctor_set_uint16(x_313, sizeof(void*)*2 + 4, x_311);
lean_ctor_set_uint8(x_313, sizeof(void*)*2 + 7, x_312);
return x_313;
}
case 6:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_314 = lean_ctor_get(x_2, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_2, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_2, 2);
lean_inc(x_316);
lean_dec(x_2);
x_317 = lean_unsigned_to_nat(1u);
x_318 = lean_nat_dec_eq(x_315, x_317);
x_319 = l_Nat_repr(x_314);
x_320 = l_Lean_IR_VarId_HasToString___closed__1;
x_321 = lean_string_append(x_320, x_319);
lean_dec(x_319);
x_322 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_322, 0, x_321);
x_323 = l_Lean_IR_formatFnBody___main(x_1, x_316);
if (x_318 == 0)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; uint32_t x_328; uint16_t x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; uint32_t x_333; uint16_t x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint32_t x_341; uint16_t x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; uint32_t x_346; uint16_t x_347; uint8_t x_348; lean_object* x_349; uint32_t x_350; uint16_t x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; uint32_t x_355; uint16_t x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; uint32_t x_360; uint16_t x_361; uint8_t x_362; lean_object* x_363; uint32_t x_364; uint16_t x_365; uint8_t x_366; lean_object* x_367; 
x_324 = l_Nat_repr(x_315);
x_325 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = 0;
x_327 = l_Lean_Format_sbracket___closed__2;
x_328 = 0;
x_329 = 0;
x_330 = 0;
x_331 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_331, 0, x_327);
lean_ctor_set(x_331, 1, x_325);
lean_ctor_set_uint8(x_331, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_331, sizeof(void*)*2, x_328);
lean_ctor_set_uint16(x_331, sizeof(void*)*2 + 4, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*2 + 7, x_330);
x_332 = l_Lean_Format_sbracket___closed__3;
x_333 = 0;
x_334 = 0;
x_335 = 0;
x_336 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_336, 0, x_331);
lean_ctor_set(x_336, 1, x_332);
lean_ctor_set_uint8(x_336, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_336, sizeof(void*)*2, x_333);
lean_ctor_set_uint16(x_336, sizeof(void*)*2 + 4, x_334);
lean_ctor_set_uint8(x_336, sizeof(void*)*2 + 7, x_335);
x_337 = l_Lean_Format_sbracket___closed__1;
x_338 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_format_group(x_338);
x_340 = l_Lean_IR_formatFnBodyHead___closed__18;
x_341 = 0;
x_342 = 0;
x_343 = 0;
x_344 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_344, 0, x_340);
lean_ctor_set(x_344, 1, x_339);
lean_ctor_set_uint8(x_344, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_344, sizeof(void*)*2, x_341);
lean_ctor_set_uint16(x_344, sizeof(void*)*2 + 4, x_342);
lean_ctor_set_uint8(x_344, sizeof(void*)*2 + 7, x_343);
x_345 = l_Lean_Format_flatten___main___closed__1;
x_346 = 0;
x_347 = 0;
x_348 = 0;
x_349 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_349, 0, x_344);
lean_ctor_set(x_349, 1, x_345);
lean_ctor_set_uint8(x_349, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_349, sizeof(void*)*2, x_346);
lean_ctor_set_uint16(x_349, sizeof(void*)*2 + 4, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*2 + 7, x_348);
x_350 = 0;
x_351 = 0;
x_352 = 0;
x_353 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_353, 0, x_349);
lean_ctor_set(x_353, 1, x_322);
lean_ctor_set_uint8(x_353, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_353, sizeof(void*)*2, x_350);
lean_ctor_set_uint16(x_353, sizeof(void*)*2 + 4, x_351);
lean_ctor_set_uint8(x_353, sizeof(void*)*2 + 7, x_352);
x_354 = l_Lean_IR_formatFnBody___main___closed__2;
x_355 = 0;
x_356 = 0;
x_357 = 0;
x_358 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set_uint8(x_358, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_358, sizeof(void*)*2, x_355);
lean_ctor_set_uint16(x_358, sizeof(void*)*2 + 4, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*2 + 7, x_357);
x_359 = lean_box(1);
x_360 = 0;
x_361 = 0;
x_362 = 0;
x_363 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_363, 0, x_358);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set_uint8(x_363, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_363, sizeof(void*)*2, x_360);
lean_ctor_set_uint16(x_363, sizeof(void*)*2 + 4, x_361);
lean_ctor_set_uint8(x_363, sizeof(void*)*2 + 7, x_362);
x_364 = 0;
x_365 = 0;
x_366 = 0;
x_367 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_367, 0, x_363);
lean_ctor_set(x_367, 1, x_323);
lean_ctor_set_uint8(x_367, sizeof(void*)*2 + 6, x_326);
lean_ctor_set_uint32(x_367, sizeof(void*)*2, x_364);
lean_ctor_set_uint16(x_367, sizeof(void*)*2 + 4, x_365);
lean_ctor_set_uint8(x_367, sizeof(void*)*2 + 7, x_366);
return x_367;
}
else
{
uint8_t x_368; lean_object* x_369; uint32_t x_370; uint16_t x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; uint32_t x_375; uint16_t x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; uint32_t x_380; uint16_t x_381; uint8_t x_382; lean_object* x_383; uint32_t x_384; uint16_t x_385; uint8_t x_386; lean_object* x_387; 
lean_dec(x_315);
x_368 = 0;
x_369 = l_Lean_IR_formatFnBodyHead___closed__20;
x_370 = 0;
x_371 = 0;
x_372 = 0;
x_373 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_373, 0, x_369);
lean_ctor_set(x_373, 1, x_322);
lean_ctor_set_uint8(x_373, sizeof(void*)*2 + 6, x_368);
lean_ctor_set_uint32(x_373, sizeof(void*)*2, x_370);
lean_ctor_set_uint16(x_373, sizeof(void*)*2 + 4, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*2 + 7, x_372);
x_374 = l_Lean_IR_formatFnBody___main___closed__2;
x_375 = 0;
x_376 = 0;
x_377 = 0;
x_378 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set_uint8(x_378, sizeof(void*)*2 + 6, x_368);
lean_ctor_set_uint32(x_378, sizeof(void*)*2, x_375);
lean_ctor_set_uint16(x_378, sizeof(void*)*2 + 4, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*2 + 7, x_377);
x_379 = lean_box(1);
x_380 = 0;
x_381 = 0;
x_382 = 0;
x_383 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_383, 0, x_378);
lean_ctor_set(x_383, 1, x_379);
lean_ctor_set_uint8(x_383, sizeof(void*)*2 + 6, x_368);
lean_ctor_set_uint32(x_383, sizeof(void*)*2, x_380);
lean_ctor_set_uint16(x_383, sizeof(void*)*2 + 4, x_381);
lean_ctor_set_uint8(x_383, sizeof(void*)*2 + 7, x_382);
x_384 = 0;
x_385 = 0;
x_386 = 0;
x_387 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_387, 0, x_383);
lean_ctor_set(x_387, 1, x_323);
lean_ctor_set_uint8(x_387, sizeof(void*)*2 + 6, x_368);
lean_ctor_set_uint32(x_387, sizeof(void*)*2, x_384);
lean_ctor_set_uint16(x_387, sizeof(void*)*2 + 4, x_385);
lean_ctor_set_uint8(x_387, sizeof(void*)*2 + 7, x_386);
return x_387;
}
}
case 7:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_388 = lean_ctor_get(x_2, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_2, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_2, 2);
lean_inc(x_390);
lean_dec(x_2);
x_391 = lean_unsigned_to_nat(1u);
x_392 = lean_nat_dec_eq(x_389, x_391);
x_393 = l_Nat_repr(x_388);
x_394 = l_Lean_IR_VarId_HasToString___closed__1;
x_395 = lean_string_append(x_394, x_393);
lean_dec(x_393);
x_396 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_396, 0, x_395);
x_397 = l_Lean_IR_formatFnBody___main(x_1, x_390);
if (x_392 == 0)
{
lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; uint32_t x_402; uint16_t x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; uint32_t x_407; uint16_t x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint32_t x_415; uint16_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; uint32_t x_420; uint16_t x_421; uint8_t x_422; lean_object* x_423; uint32_t x_424; uint16_t x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; uint32_t x_429; uint16_t x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; uint32_t x_434; uint16_t x_435; uint8_t x_436; lean_object* x_437; uint32_t x_438; uint16_t x_439; uint8_t x_440; lean_object* x_441; 
x_398 = l_Nat_repr(x_389);
x_399 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_399, 0, x_398);
x_400 = 0;
x_401 = l_Lean_Format_sbracket___closed__2;
x_402 = 0;
x_403 = 0;
x_404 = 0;
x_405 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_405, 0, x_401);
lean_ctor_set(x_405, 1, x_399);
lean_ctor_set_uint8(x_405, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_405, sizeof(void*)*2, x_402);
lean_ctor_set_uint16(x_405, sizeof(void*)*2 + 4, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*2 + 7, x_404);
x_406 = l_Lean_Format_sbracket___closed__3;
x_407 = 0;
x_408 = 0;
x_409 = 0;
x_410 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_410, sizeof(void*)*2, x_407);
lean_ctor_set_uint16(x_410, sizeof(void*)*2 + 4, x_408);
lean_ctor_set_uint8(x_410, sizeof(void*)*2 + 7, x_409);
x_411 = l_Lean_Format_sbracket___closed__1;
x_412 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_410);
x_413 = lean_format_group(x_412);
x_414 = l_Lean_IR_formatFnBodyHead___closed__22;
x_415 = 0;
x_416 = 0;
x_417 = 0;
x_418 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_413);
lean_ctor_set_uint8(x_418, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_418, sizeof(void*)*2, x_415);
lean_ctor_set_uint16(x_418, sizeof(void*)*2 + 4, x_416);
lean_ctor_set_uint8(x_418, sizeof(void*)*2 + 7, x_417);
x_419 = l_Lean_Format_flatten___main___closed__1;
x_420 = 0;
x_421 = 0;
x_422 = 0;
x_423 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_423, 0, x_418);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set_uint8(x_423, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_423, sizeof(void*)*2, x_420);
lean_ctor_set_uint16(x_423, sizeof(void*)*2 + 4, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*2 + 7, x_422);
x_424 = 0;
x_425 = 0;
x_426 = 0;
x_427 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_427, 0, x_423);
lean_ctor_set(x_427, 1, x_396);
lean_ctor_set_uint8(x_427, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_427, sizeof(void*)*2, x_424);
lean_ctor_set_uint16(x_427, sizeof(void*)*2 + 4, x_425);
lean_ctor_set_uint8(x_427, sizeof(void*)*2 + 7, x_426);
x_428 = l_Lean_IR_formatFnBody___main___closed__2;
x_429 = 0;
x_430 = 0;
x_431 = 0;
x_432 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_432, 0, x_427);
lean_ctor_set(x_432, 1, x_428);
lean_ctor_set_uint8(x_432, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_432, sizeof(void*)*2, x_429);
lean_ctor_set_uint16(x_432, sizeof(void*)*2 + 4, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*2 + 7, x_431);
x_433 = lean_box(1);
x_434 = 0;
x_435 = 0;
x_436 = 0;
x_437 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_433);
lean_ctor_set_uint8(x_437, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_437, sizeof(void*)*2, x_434);
lean_ctor_set_uint16(x_437, sizeof(void*)*2 + 4, x_435);
lean_ctor_set_uint8(x_437, sizeof(void*)*2 + 7, x_436);
x_438 = 0;
x_439 = 0;
x_440 = 0;
x_441 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_441, 0, x_437);
lean_ctor_set(x_441, 1, x_397);
lean_ctor_set_uint8(x_441, sizeof(void*)*2 + 6, x_400);
lean_ctor_set_uint32(x_441, sizeof(void*)*2, x_438);
lean_ctor_set_uint16(x_441, sizeof(void*)*2 + 4, x_439);
lean_ctor_set_uint8(x_441, sizeof(void*)*2 + 7, x_440);
return x_441;
}
else
{
uint8_t x_442; lean_object* x_443; uint32_t x_444; uint16_t x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; uint32_t x_449; uint16_t x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; uint32_t x_454; uint16_t x_455; uint8_t x_456; lean_object* x_457; uint32_t x_458; uint16_t x_459; uint8_t x_460; lean_object* x_461; 
lean_dec(x_389);
x_442 = 0;
x_443 = l_Lean_IR_formatFnBodyHead___closed__24;
x_444 = 0;
x_445 = 0;
x_446 = 0;
x_447 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_447, 0, x_443);
lean_ctor_set(x_447, 1, x_396);
lean_ctor_set_uint8(x_447, sizeof(void*)*2 + 6, x_442);
lean_ctor_set_uint32(x_447, sizeof(void*)*2, x_444);
lean_ctor_set_uint16(x_447, sizeof(void*)*2 + 4, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*2 + 7, x_446);
x_448 = l_Lean_IR_formatFnBody___main___closed__2;
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_452, 0, x_447);
lean_ctor_set(x_452, 1, x_448);
lean_ctor_set_uint8(x_452, sizeof(void*)*2 + 6, x_442);
lean_ctor_set_uint32(x_452, sizeof(void*)*2, x_449);
lean_ctor_set_uint16(x_452, sizeof(void*)*2 + 4, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*2 + 7, x_451);
x_453 = lean_box(1);
x_454 = 0;
x_455 = 0;
x_456 = 0;
x_457 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_457, 0, x_452);
lean_ctor_set(x_457, 1, x_453);
lean_ctor_set_uint8(x_457, sizeof(void*)*2 + 6, x_442);
lean_ctor_set_uint32(x_457, sizeof(void*)*2, x_454);
lean_ctor_set_uint16(x_457, sizeof(void*)*2 + 4, x_455);
lean_ctor_set_uint8(x_457, sizeof(void*)*2 + 7, x_456);
x_458 = 0;
x_459 = 0;
x_460 = 0;
x_461 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_461, 0, x_457);
lean_ctor_set(x_461, 1, x_397);
lean_ctor_set_uint8(x_461, sizeof(void*)*2 + 6, x_442);
lean_ctor_set_uint32(x_461, sizeof(void*)*2, x_458);
lean_ctor_set_uint16(x_461, sizeof(void*)*2 + 4, x_459);
lean_ctor_set_uint8(x_461, sizeof(void*)*2 + 7, x_460);
return x_461;
}
}
case 8:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; uint32_t x_470; uint16_t x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; uint32_t x_475; uint16_t x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; uint32_t x_480; uint16_t x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint32_t x_485; uint16_t x_486; uint8_t x_487; lean_object* x_488; 
x_462 = lean_ctor_get(x_2, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_2, 1);
lean_inc(x_463);
lean_dec(x_2);
x_464 = l_Nat_repr(x_462);
x_465 = l_Lean_IR_VarId_HasToString___closed__1;
x_466 = lean_string_append(x_465, x_464);
lean_dec(x_464);
x_467 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_467, 0, x_466);
x_468 = 0;
x_469 = l_Lean_IR_formatFnBodyHead___closed__26;
x_470 = 0;
x_471 = 0;
x_472 = 0;
x_473 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_473, 0, x_469);
lean_ctor_set(x_473, 1, x_467);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 6, x_468);
lean_ctor_set_uint32(x_473, sizeof(void*)*2, x_470);
lean_ctor_set_uint16(x_473, sizeof(void*)*2 + 4, x_471);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 7, x_472);
x_474 = l_Lean_IR_formatFnBody___main___closed__2;
x_475 = 0;
x_476 = 0;
x_477 = 0;
x_478 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_478, 0, x_473);
lean_ctor_set(x_478, 1, x_474);
lean_ctor_set_uint8(x_478, sizeof(void*)*2 + 6, x_468);
lean_ctor_set_uint32(x_478, sizeof(void*)*2, x_475);
lean_ctor_set_uint16(x_478, sizeof(void*)*2 + 4, x_476);
lean_ctor_set_uint8(x_478, sizeof(void*)*2 + 7, x_477);
x_479 = lean_box(1);
x_480 = 0;
x_481 = 0;
x_482 = 0;
x_483 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_483, 0, x_478);
lean_ctor_set(x_483, 1, x_479);
lean_ctor_set_uint8(x_483, sizeof(void*)*2 + 6, x_468);
lean_ctor_set_uint32(x_483, sizeof(void*)*2, x_480);
lean_ctor_set_uint16(x_483, sizeof(void*)*2 + 4, x_481);
lean_ctor_set_uint8(x_483, sizeof(void*)*2 + 7, x_482);
x_484 = l_Lean_IR_formatFnBody___main(x_1, x_463);
x_485 = 0;
x_486 = 0;
x_487 = 0;
x_488 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_488, 0, x_483);
lean_ctor_set(x_488, 1, x_484);
lean_ctor_set_uint8(x_488, sizeof(void*)*2 + 6, x_468);
lean_ctor_set_uint32(x_488, sizeof(void*)*2, x_485);
lean_ctor_set_uint16(x_488, sizeof(void*)*2 + 4, x_486);
lean_ctor_set_uint8(x_488, sizeof(void*)*2 + 7, x_487);
return x_488;
}
case 9:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; uint32_t x_494; uint16_t x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; uint32_t x_499; uint16_t x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; uint32_t x_504; uint16_t x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; uint32_t x_509; uint16_t x_510; uint8_t x_511; lean_object* x_512; 
x_489 = lean_ctor_get(x_2, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_2, 1);
lean_inc(x_490);
lean_dec(x_2);
x_491 = l_Lean_formatKVMap(x_489);
x_492 = 0;
x_493 = l_Lean_IR_formatFnBodyHead___closed__28;
x_494 = 0;
x_495 = 0;
x_496 = 0;
x_497 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_497, 0, x_493);
lean_ctor_set(x_497, 1, x_491);
lean_ctor_set_uint8(x_497, sizeof(void*)*2 + 6, x_492);
lean_ctor_set_uint32(x_497, sizeof(void*)*2, x_494);
lean_ctor_set_uint16(x_497, sizeof(void*)*2 + 4, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*2 + 7, x_496);
x_498 = l_Lean_IR_formatFnBody___main___closed__2;
x_499 = 0;
x_500 = 0;
x_501 = 0;
x_502 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_502, 0, x_497);
lean_ctor_set(x_502, 1, x_498);
lean_ctor_set_uint8(x_502, sizeof(void*)*2 + 6, x_492);
lean_ctor_set_uint32(x_502, sizeof(void*)*2, x_499);
lean_ctor_set_uint16(x_502, sizeof(void*)*2 + 4, x_500);
lean_ctor_set_uint8(x_502, sizeof(void*)*2 + 7, x_501);
x_503 = lean_box(1);
x_504 = 0;
x_505 = 0;
x_506 = 0;
x_507 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_507, 0, x_502);
lean_ctor_set(x_507, 1, x_503);
lean_ctor_set_uint8(x_507, sizeof(void*)*2 + 6, x_492);
lean_ctor_set_uint32(x_507, sizeof(void*)*2, x_504);
lean_ctor_set_uint16(x_507, sizeof(void*)*2 + 4, x_505);
lean_ctor_set_uint8(x_507, sizeof(void*)*2 + 7, x_506);
x_508 = l_Lean_IR_formatFnBody___main(x_1, x_490);
x_509 = 0;
x_510 = 0;
x_511 = 0;
x_512 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_512, 0, x_507);
lean_ctor_set(x_512, 1, x_508);
lean_ctor_set_uint8(x_512, sizeof(void*)*2 + 6, x_492);
lean_ctor_set_uint32(x_512, sizeof(void*)*2, x_509);
lean_ctor_set_uint16(x_512, sizeof(void*)*2 + 4, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*2 + 7, x_511);
return x_512;
}
case 10:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; uint32_t x_522; uint16_t x_523; uint8_t x_524; lean_object* x_525; lean_object* x_526; uint32_t x_527; uint16_t x_528; uint8_t x_529; lean_object* x_530; lean_object* x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; lean_object* x_536; uint32_t x_537; uint16_t x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint32_t x_544; uint16_t x_545; uint8_t x_546; lean_object* x_547; 
x_513 = lean_ctor_get(x_2, 1);
lean_inc(x_513);
x_514 = lean_ctor_get(x_2, 2);
lean_inc(x_514);
x_515 = lean_ctor_get(x_2, 3);
lean_inc(x_515);
lean_dec(x_2);
x_516 = l_Nat_repr(x_513);
x_517 = l_Lean_IR_VarId_HasToString___closed__1;
x_518 = lean_string_append(x_517, x_516);
lean_dec(x_516);
x_519 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_519, 0, x_518);
x_520 = 0;
x_521 = l_Lean_IR_formatFnBodyHead___closed__30;
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_525, 0, x_521);
lean_ctor_set(x_525, 1, x_519);
lean_ctor_set_uint8(x_525, sizeof(void*)*2 + 6, x_520);
lean_ctor_set_uint32(x_525, sizeof(void*)*2, x_522);
lean_ctor_set_uint16(x_525, sizeof(void*)*2 + 4, x_523);
lean_ctor_set_uint8(x_525, sizeof(void*)*2 + 7, x_524);
x_526 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_527 = 0;
x_528 = 0;
x_529 = 0;
x_530 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_530, 0, x_525);
lean_ctor_set(x_530, 1, x_526);
lean_ctor_set_uint8(x_530, sizeof(void*)*2 + 6, x_520);
lean_ctor_set_uint32(x_530, sizeof(void*)*2, x_527);
lean_ctor_set_uint16(x_530, sizeof(void*)*2 + 4, x_528);
lean_ctor_set_uint8(x_530, sizeof(void*)*2 + 7, x_529);
x_531 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_514);
lean_dec(x_514);
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_535, 0, x_530);
lean_ctor_set(x_535, 1, x_531);
lean_ctor_set_uint8(x_535, sizeof(void*)*2 + 6, x_520);
lean_ctor_set_uint32(x_535, sizeof(void*)*2, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*2 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*2 + 7, x_534);
x_536 = l_Lean_IR_formatFnBody___main___closed__6;
x_537 = 0;
x_538 = 0;
x_539 = 0;
x_540 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 6, x_520);
lean_ctor_set_uint32(x_540, sizeof(void*)*2, x_537);
lean_ctor_set_uint16(x_540, sizeof(void*)*2 + 4, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 7, x_539);
x_541 = lean_unsigned_to_nat(0u);
x_542 = lean_box(0);
x_543 = l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_515, x_515, x_541, x_542);
lean_dec(x_515);
x_544 = 0;
x_545 = 0;
x_546 = 0;
x_547 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_547, 0, x_540);
lean_ctor_set(x_547, 1, x_543);
lean_ctor_set_uint8(x_547, sizeof(void*)*2 + 6, x_520);
lean_ctor_set_uint32(x_547, sizeof(void*)*2, x_544);
lean_ctor_set_uint16(x_547, sizeof(void*)*2 + 4, x_545);
lean_ctor_set_uint8(x_547, sizeof(void*)*2 + 7, x_546);
return x_547;
}
case 11:
{
lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; uint32_t x_552; uint16_t x_553; uint8_t x_554; lean_object* x_555; 
lean_dec(x_1);
x_548 = lean_ctor_get(x_2, 0);
lean_inc(x_548);
lean_dec(x_2);
x_549 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_548);
x_550 = 0;
x_551 = l_Lean_IR_formatFnBodyHead___closed__34;
x_552 = 0;
x_553 = 0;
x_554 = 0;
x_555 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_555, 0, x_551);
lean_ctor_set(x_555, 1, x_549);
lean_ctor_set_uint8(x_555, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_555, sizeof(void*)*2, x_552);
lean_ctor_set_uint16(x_555, sizeof(void*)*2 + 4, x_553);
lean_ctor_set_uint8(x_555, sizeof(void*)*2 + 7, x_554);
return x_555;
}
case 12:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; lean_object* x_563; uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint32_t x_571; uint16_t x_572; uint8_t x_573; lean_object* x_574; 
lean_dec(x_1);
x_556 = lean_ctor_get(x_2, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_2, 1);
lean_inc(x_557);
lean_dec(x_2);
x_558 = l_Nat_repr(x_556);
x_559 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_560 = lean_string_append(x_559, x_558);
lean_dec(x_558);
x_561 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_561, 0, x_560);
x_562 = 0;
x_563 = l_Lean_IR_formatFnBodyHead___closed__36;
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_567, 0, x_563);
lean_ctor_set(x_567, 1, x_561);
lean_ctor_set_uint8(x_567, sizeof(void*)*2 + 6, x_562);
lean_ctor_set_uint32(x_567, sizeof(void*)*2, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*2 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*2 + 7, x_566);
x_568 = lean_unsigned_to_nat(0u);
x_569 = lean_box(0);
x_570 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_557, x_557, x_568, x_569);
lean_dec(x_557);
x_571 = 0;
x_572 = 0;
x_573 = 0;
x_574 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_574, 0, x_567);
lean_ctor_set(x_574, 1, x_570);
lean_ctor_set_uint8(x_574, sizeof(void*)*2 + 6, x_562);
lean_ctor_set_uint32(x_574, sizeof(void*)*2, x_571);
lean_ctor_set_uint16(x_574, sizeof(void*)*2 + 4, x_572);
lean_ctor_set_uint8(x_574, sizeof(void*)*2 + 7, x_573);
return x_574;
}
default: 
{
lean_object* x_575; 
lean_dec(x_1);
x_575 = l_Lean_IR_formatFnBodyHead___closed__38;
return x_575;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_formatFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_formatFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_fnBodyHasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_closure((void*)(l_Lean_IR_formatFnBody), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_fnBodyHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_fnBodyHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_fnBodyHasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatFnBody___main(x_2, x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatDecl___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extern ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatDecl___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint32_t x_12; uint16_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint16_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint16_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint16_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; uint16_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint16_t x_46; uint8_t x_47; lean_object* x_48; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_3);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_IR_formatDecl___closed__2;
x_12 = 0;
x_13 = 0;
x_14 = 0;
x_15 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_15, sizeof(void*)*2, x_12);
lean_ctor_set_uint16(x_15, sizeof(void*)*2 + 4, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 7, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_box(0);
x_18 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_16, x_17);
lean_dec(x_4);
x_19 = 0;
x_20 = 0;
x_21 = 0;
x_22 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_22, sizeof(void*)*2, x_19);
lean_ctor_set_uint16(x_22, sizeof(void*)*2 + 4, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 7, x_21);
x_23 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_24 = 0;
x_25 = 0;
x_26 = 0;
x_27 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_27, sizeof(void*)*2, x_24);
lean_ctor_set_uint16(x_27, sizeof(void*)*2 + 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 7, x_26);
x_28 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_5);
lean_dec(x_5);
x_29 = 0;
x_30 = 0;
x_31 = 0;
x_32 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_uint16(x_32, sizeof(void*)*2 + 4, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 7, x_31);
x_33 = l_Lean_IR_formatFnBody___main___closed__4;
x_34 = 0;
x_35 = 0;
x_36 = 0;
x_37 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_37, sizeof(void*)*2, x_34);
lean_ctor_set_uint16(x_37, sizeof(void*)*2 + 4, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 7, x_36);
lean_inc(x_1);
x_38 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_39 = lean_box(1);
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_43, sizeof(void*)*2, x_40);
lean_ctor_set_uint16(x_43, sizeof(void*)*2 + 4, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 7, x_42);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 6, x_10);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_uint16(x_48, sizeof(void*)*2 + 4, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 7, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint32_t x_57; uint16_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; uint16_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint32_t x_74; uint16_t x_75; uint8_t x_76; lean_object* x_77; 
lean_dec(x_1);
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
lean_dec(x_2);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_49);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = 0;
x_56 = l_Lean_IR_formatDecl___closed__4;
x_57 = 0;
x_58 = 0;
x_59 = 0;
x_60 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 6, x_55);
lean_ctor_set_uint32(x_60, sizeof(void*)*2, x_57);
lean_ctor_set_uint16(x_60, sizeof(void*)*2 + 4, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 7, x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_box(0);
x_63 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_50, x_50, x_61, x_62);
lean_dec(x_50);
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 6, x_55);
lean_ctor_set_uint32(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_uint16(x_67, sizeof(void*)*2 + 4, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 7, x_66);
x_68 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 6, x_55);
lean_ctor_set_uint32(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_uint16(x_72, sizeof(void*)*2 + 4, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 7, x_71);
x_73 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_51);
lean_dec(x_51);
x_74 = 0;
x_75 = 0;
x_76 = 0;
x_77 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 6, x_55);
lean_ctor_set_uint32(x_77, sizeof(void*)*2, x_74);
lean_ctor_set_uint16(x_77, sizeof(void*)*2 + 4, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 7, x_76);
return x_77;
}
}
}
lean_object* _init_l_Lean_IR_declHasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_closure((void*)(l_Lean_IR_formatDecl), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_declHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declHasFormat___closed__1;
return x_1;
}
}
lean_object* lean_ir_decl_to_string(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatDecl(x_2, x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_declHasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_ir_decl_to_string), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_declHasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declHasToString___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Lean_Data_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1 = _init_l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1);
l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2 = _init_l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2);
l_Lean_IR_argHasFormat___closed__1 = _init_l_Lean_IR_argHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_argHasFormat___closed__1);
l_Lean_IR_argHasFormat = _init_l_Lean_IR_argHasFormat();
lean_mark_persistent(l_Lean_IR_argHasFormat);
l_Lean_IR_litValHasFormat___closed__1 = _init_l_Lean_IR_litValHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_litValHasFormat___closed__1);
l_Lean_IR_litValHasFormat = _init_l_Lean_IR_litValHasFormat();
lean_mark_persistent(l_Lean_IR_litValHasFormat);
l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1 = _init_l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1);
l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2 = _init_l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2);
l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3 = _init_l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3);
l_Lean_IR_ctorInfoHasFormat___closed__1 = _init_l_Lean_IR_ctorInfoHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_ctorInfoHasFormat___closed__1);
l_Lean_IR_ctorInfoHasFormat = _init_l_Lean_IR_ctorInfoHasFormat();
lean_mark_persistent(l_Lean_IR_ctorInfoHasFormat);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31);
l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32 = _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32);
l_Lean_IR_exprHasFormat___closed__1 = _init_l_Lean_IR_exprHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_exprHasFormat___closed__1);
l_Lean_IR_exprHasFormat = _init_l_Lean_IR_exprHasFormat();
lean_mark_persistent(l_Lean_IR_exprHasFormat);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22);
l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23 = _init_l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23);
l_Lean_IR_typeHasFormat___closed__1 = _init_l_Lean_IR_typeHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_typeHasFormat___closed__1);
l_Lean_IR_typeHasFormat = _init_l_Lean_IR_typeHasFormat();
lean_mark_persistent(l_Lean_IR_typeHasFormat);
l_Lean_IR_typeHasToString___closed__1 = _init_l_Lean_IR_typeHasToString___closed__1();
lean_mark_persistent(l_Lean_IR_typeHasToString___closed__1);
l_Lean_IR_typeHasToString = _init_l_Lean_IR_typeHasToString();
lean_mark_persistent(l_Lean_IR_typeHasToString);
l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1 = _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1);
l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2 = _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2);
l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3 = _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3);
l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4 = _init_l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4);
l_Lean_IR_paramHasFormat___closed__1 = _init_l_Lean_IR_paramHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_paramHasFormat___closed__1);
l_Lean_IR_paramHasFormat = _init_l_Lean_IR_paramHasFormat();
lean_mark_persistent(l_Lean_IR_paramHasFormat);
l_Lean_IR_formatAlt___closed__1 = _init_l_Lean_IR_formatAlt___closed__1();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__1);
l_Lean_IR_formatAlt___closed__2 = _init_l_Lean_IR_formatAlt___closed__2();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__2);
l_Lean_IR_formatAlt___closed__3 = _init_l_Lean_IR_formatAlt___closed__3();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__3);
l_Lean_IR_formatAlt___closed__4 = _init_l_Lean_IR_formatAlt___closed__4();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__4);
l_Lean_IR_formatFnBodyHead___closed__1 = _init_l_Lean_IR_formatFnBodyHead___closed__1();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__1);
l_Lean_IR_formatFnBodyHead___closed__2 = _init_l_Lean_IR_formatFnBodyHead___closed__2();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__2);
l_Lean_IR_formatFnBodyHead___closed__3 = _init_l_Lean_IR_formatFnBodyHead___closed__3();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__3);
l_Lean_IR_formatFnBodyHead___closed__4 = _init_l_Lean_IR_formatFnBodyHead___closed__4();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__4);
l_Lean_IR_formatFnBodyHead___closed__5 = _init_l_Lean_IR_formatFnBodyHead___closed__5();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__5);
l_Lean_IR_formatFnBodyHead___closed__6 = _init_l_Lean_IR_formatFnBodyHead___closed__6();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__6);
l_Lean_IR_formatFnBodyHead___closed__7 = _init_l_Lean_IR_formatFnBodyHead___closed__7();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__7);
l_Lean_IR_formatFnBodyHead___closed__8 = _init_l_Lean_IR_formatFnBodyHead___closed__8();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__8);
l_Lean_IR_formatFnBodyHead___closed__9 = _init_l_Lean_IR_formatFnBodyHead___closed__9();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__9);
l_Lean_IR_formatFnBodyHead___closed__10 = _init_l_Lean_IR_formatFnBodyHead___closed__10();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__10);
l_Lean_IR_formatFnBodyHead___closed__11 = _init_l_Lean_IR_formatFnBodyHead___closed__11();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__11);
l_Lean_IR_formatFnBodyHead___closed__12 = _init_l_Lean_IR_formatFnBodyHead___closed__12();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__12);
l_Lean_IR_formatFnBodyHead___closed__13 = _init_l_Lean_IR_formatFnBodyHead___closed__13();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__13);
l_Lean_IR_formatFnBodyHead___closed__14 = _init_l_Lean_IR_formatFnBodyHead___closed__14();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__14);
l_Lean_IR_formatFnBodyHead___closed__15 = _init_l_Lean_IR_formatFnBodyHead___closed__15();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__15);
l_Lean_IR_formatFnBodyHead___closed__16 = _init_l_Lean_IR_formatFnBodyHead___closed__16();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__16);
l_Lean_IR_formatFnBodyHead___closed__17 = _init_l_Lean_IR_formatFnBodyHead___closed__17();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__17);
l_Lean_IR_formatFnBodyHead___closed__18 = _init_l_Lean_IR_formatFnBodyHead___closed__18();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__18);
l_Lean_IR_formatFnBodyHead___closed__19 = _init_l_Lean_IR_formatFnBodyHead___closed__19();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__19);
l_Lean_IR_formatFnBodyHead___closed__20 = _init_l_Lean_IR_formatFnBodyHead___closed__20();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__20);
l_Lean_IR_formatFnBodyHead___closed__21 = _init_l_Lean_IR_formatFnBodyHead___closed__21();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__21);
l_Lean_IR_formatFnBodyHead___closed__22 = _init_l_Lean_IR_formatFnBodyHead___closed__22();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__22);
l_Lean_IR_formatFnBodyHead___closed__23 = _init_l_Lean_IR_formatFnBodyHead___closed__23();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__23);
l_Lean_IR_formatFnBodyHead___closed__24 = _init_l_Lean_IR_formatFnBodyHead___closed__24();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__24);
l_Lean_IR_formatFnBodyHead___closed__25 = _init_l_Lean_IR_formatFnBodyHead___closed__25();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__25);
l_Lean_IR_formatFnBodyHead___closed__26 = _init_l_Lean_IR_formatFnBodyHead___closed__26();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__26);
l_Lean_IR_formatFnBodyHead___closed__27 = _init_l_Lean_IR_formatFnBodyHead___closed__27();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__27);
l_Lean_IR_formatFnBodyHead___closed__28 = _init_l_Lean_IR_formatFnBodyHead___closed__28();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__28);
l_Lean_IR_formatFnBodyHead___closed__29 = _init_l_Lean_IR_formatFnBodyHead___closed__29();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__29);
l_Lean_IR_formatFnBodyHead___closed__30 = _init_l_Lean_IR_formatFnBodyHead___closed__30();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__30);
l_Lean_IR_formatFnBodyHead___closed__31 = _init_l_Lean_IR_formatFnBodyHead___closed__31();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__31);
l_Lean_IR_formatFnBodyHead___closed__32 = _init_l_Lean_IR_formatFnBodyHead___closed__32();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__32);
l_Lean_IR_formatFnBodyHead___closed__33 = _init_l_Lean_IR_formatFnBodyHead___closed__33();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__33);
l_Lean_IR_formatFnBodyHead___closed__34 = _init_l_Lean_IR_formatFnBodyHead___closed__34();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__34);
l_Lean_IR_formatFnBodyHead___closed__35 = _init_l_Lean_IR_formatFnBodyHead___closed__35();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__35);
l_Lean_IR_formatFnBodyHead___closed__36 = _init_l_Lean_IR_formatFnBodyHead___closed__36();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__36);
l_Lean_IR_formatFnBodyHead___closed__37 = _init_l_Lean_IR_formatFnBodyHead___closed__37();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__37);
l_Lean_IR_formatFnBodyHead___closed__38 = _init_l_Lean_IR_formatFnBodyHead___closed__38();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__38);
l_Lean_IR_formatFnBody___main___closed__1 = _init_l_Lean_IR_formatFnBody___main___closed__1();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__1);
l_Lean_IR_formatFnBody___main___closed__2 = _init_l_Lean_IR_formatFnBody___main___closed__2();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__2);
l_Lean_IR_formatFnBody___main___closed__3 = _init_l_Lean_IR_formatFnBody___main___closed__3();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__3);
l_Lean_IR_formatFnBody___main___closed__4 = _init_l_Lean_IR_formatFnBody___main___closed__4();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__4);
l_Lean_IR_formatFnBody___main___closed__5 = _init_l_Lean_IR_formatFnBody___main___closed__5();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__5);
l_Lean_IR_formatFnBody___main___closed__6 = _init_l_Lean_IR_formatFnBody___main___closed__6();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__6);
l_Lean_IR_fnBodyHasFormat___closed__1 = _init_l_Lean_IR_fnBodyHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_fnBodyHasFormat___closed__1);
l_Lean_IR_fnBodyHasFormat = _init_l_Lean_IR_fnBodyHasFormat();
lean_mark_persistent(l_Lean_IR_fnBodyHasFormat);
l_Lean_IR_formatDecl___closed__1 = _init_l_Lean_IR_formatDecl___closed__1();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__1);
l_Lean_IR_formatDecl___closed__2 = _init_l_Lean_IR_formatDecl___closed__2();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__2);
l_Lean_IR_formatDecl___closed__3 = _init_l_Lean_IR_formatDecl___closed__3();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__3);
l_Lean_IR_formatDecl___closed__4 = _init_l_Lean_IR_formatDecl___closed__4();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__4);
l_Lean_IR_declHasFormat___closed__1 = _init_l_Lean_IR_declHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_declHasFormat___closed__1);
l_Lean_IR_declHasFormat = _init_l_Lean_IR_declHasFormat();
lean_mark_persistent(l_Lean_IR_declHasFormat);
l_Lean_IR_declHasToString___closed__1 = _init_l_Lean_IR_declHasToString___closed__1();
lean_mark_persistent(l_Lean_IR_declHasToString___closed__1);
l_Lean_IR_declHasToString = _init_l_Lean_IR_declHasToString();
lean_mark_persistent(l_Lean_IR_declHasToString);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
