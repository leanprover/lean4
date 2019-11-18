// Lean compiler output
// Module: Init.Lean.Compiler.IR.Format
// Imports: Init.Lean.Compiler.IR.Basic Init.Lean.Format
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
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20;
lean_object* l_Lean_IR_formatAlt___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2;
lean_object* l_Lean_IR_formatAlt(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17;
lean_object* l_Lean_IR_formatFnBody___main___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15;
uint8_t l_Lean_Name_beq___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__21;
lean_object* l_Lean_IR_formatFnBodyHead___closed__2;
lean_object* l_Lean_IR_formatFnBodyHead___closed__36;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
lean_object* l_Lean_formatKVMap(lean_object*);
lean_object* l_Lean_IR_formatDecl___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__7;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4;
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13;
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2;
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__31;
lean_object* l_Lean_IR_typeHasFormat___closed__1;
lean_object* l_Lean_IR_formatAlt___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_argHasFormat___closed__1;
lean_object* l_Lean_IR_formatAlt___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
lean_object* l_Lean_IR_formatFnBodyHead___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__27;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam(lean_object*);
lean_object* l_Lean_IR_formatParams___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object*);
lean_object* l_Lean_IR_formatFnBody___main___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___boxed(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__29;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13;
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__32;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26;
lean_object* lean_ir_decl_to_string(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28;
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg(lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__8;
lean_object* l_Lean_IR_formatFnBodyHead___closed__38;
lean_object* l_Lean_IR_formatFnBodyHead___closed__4;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_IR_formatFnBodyHead___closed__24;
lean_object* l_Lean_IR_paramHasFormat___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___boxed(lean_object*);
lean_object* l_Lean_IR_declHasFormat;
lean_object* l_Lean_IR_fnBodyHasFormat___closed__1;
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_IR_ctorInfoHasFormat___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_exprHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__35;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__30;
lean_object* l_Lean_IR_argHasFormat;
extern lean_object* l_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1(lean_object*);
lean_object* l_Lean_IR_typeHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__27;
lean_object* l_Lean_IR_formatArray(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__21;
lean_object* l_Lean_IR_formatFnBodyHead___closed__11;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12;
lean_object* lean_ir_format_fn_body_head(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_fnBodyHasFormat;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__25;
lean_object* l_Lean_IR_formatDecl___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__15;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
lean_object* l_Lean_IR_formatFnBodyHead___closed__15;
lean_object* l_Lean_IR_formatFnBody___main___closed__3;
lean_object* l_Lean_IR_formatFnBodyHead___closed__13;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_litValHasFormat___closed__1;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__10;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__19;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_IR_formatFnBodyHead___closed__16;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__23;
lean_object* l_Lean_IR_declHasToString___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__26;
lean_object* l_Lean_IR_formatArray___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_formatFnBody___main___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__34;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2;
lean_object* l_Lean_IR_formatArray___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_declHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__12;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__17;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__5;
lean_object* l_Lean_IR_declHasToString;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3;
lean_object* l_Lean_IR_formatArray___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__23;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_IR_formatDecl___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_IR_formatFnBody___main___closed__5;
lean_object* l_Lean_IR_formatFnBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_ctorInfoHasFormat;
extern lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__3;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9;
lean_object* lean_format_group(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4;
lean_object* l_Lean_IR_formatFnBodyHead___closed__37;
lean_object* l_Lean_IR_exprHasToString(lean_object*);
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__14;
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_exprHasFormat;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatParams(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__11;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23;
lean_object* l_Lean_IR_formatFnBodyHead___closed__3;
lean_object* l_Lean_IR_formatFnBodyHead___closed__5;
lean_object* l_Lean_IR_formatFnBodyHead___closed__22;
lean_object* l_Lean_IR_litValHasFormat;
lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2;
lean_object* l_Lean_IR_fnBodyHasToString(lean_object*);
lean_object* l_Lean_IR_formatAlt___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__20;
lean_object* l___private_Init_Lean_Compiler_IR_Format_2__formatLitVal(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__19;
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(lean_object*);
lean_object* l_Lean_IR_formatDecl___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__7;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__25;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_IR_paramHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__31;
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__29;
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24;
lean_object* l_Lean_IR_formatFnBody___main___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16;
lean_object* l_Lean_IR_formatFnBodyHead___closed__17;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7;
lean_object* l_Lean_IR_formatFnBodyHead___closed__33;
lean_object* l_Lean_IR_formatFnBodyHead___closed__28;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_IR_formatFnBody___main(lean_object*, lean_object*);
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
x_10 = l_Lean_Format_flatten___main___closed__1;
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_8);
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
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
x_1 = l_System_FilePath_dirName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
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
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_4);
x_13 = lean_box(0);
x_14 = l_Lean_Name_beq___main(x_2, x_13);
if (x_12 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_11, x_5);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = l_Lean_Format_sbracket___closed__2;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_8);
x_18 = l_System_FilePath_dirName___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_2);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_8);
x_22 = l_Lean_Format_sbracket___closed__3;
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_8);
return x_23;
}
else
{
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_8);
x_26 = l_Nat_repr(x_4);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_8);
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_8);
x_30 = l_Nat_repr(x_5);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_8);
if (x_14 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = l_Lean_Format_sbracket___closed__2;
x_34 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_8);
x_35 = l_System_FilePath_dirName___closed__1;
x_36 = l_Lean_Name_toStringWithSep___main(x_35, x_2);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_8);
x_39 = l_Lean_Format_sbracket___closed__3;
x_40 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_8);
return x_40;
}
else
{
lean_dec(x_2);
return x_32;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_8);
x_43 = l_Nat_repr(x_4);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_8);
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_8);
x_47 = l_Nat_repr(x_5);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_8);
if (x_14 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = l_Lean_Format_sbracket___closed__2;
x_51 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_8);
x_52 = l_System_FilePath_dirName___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_2);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_8);
x_56 = l_Lean_Format_sbracket___closed__3;
x_57 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_8);
return x_57;
}
else
{
lean_dec(x_2);
return x_49;
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_7);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
x_3 = l_Lean_Format_join___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__9;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
x_3 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__12;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__13;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
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
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Nat_repr(x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = 0;
x_15 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__2;
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
x_17 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_18 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_14);
x_19 = l_Nat_repr(x_11);
x_20 = l_Lean_IR_VarId_HasToString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_14);
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Nat_repr(x_24);
x_29 = l_Lean_IR_VarId_HasToString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Init_Lean_Compiler_IR_Format_3__formatCtorInfo(x_25);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_box(0);
x_35 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_27, x_27, x_33, x_34);
lean_dec(x_27);
if (x_26 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = 0;
x_37 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__10;
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_36);
x_39 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
x_40 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_36);
x_41 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_36);
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_36);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = 0;
x_44 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__14;
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_31);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_43);
x_46 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_43);
x_48 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_32);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_43);
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_43);
return x_49;
}
}
case 3:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_52 = l_Nat_repr(x_50);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = 0;
x_55 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__16;
x_56 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_54);
x_57 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_54);
x_59 = l_Nat_repr(x_51);
x_60 = l_Lean_IR_VarId_HasToString___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_54);
return x_63;
}
case 4:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
lean_dec(x_1);
x_66 = l_Nat_repr(x_64);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = 0;
x_69 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__18;
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_68);
x_71 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_68);
x_73 = l_Nat_repr(x_65);
x_74 = l_Lean_IR_VarId_HasToString___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_68);
return x_77;
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 2);
lean_inc(x_80);
lean_dec(x_1);
x_81 = l_Nat_repr(x_78);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = 0;
x_84 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__20;
x_85 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_83);
x_86 = l_Lean_formatKVMap___closed__1;
x_87 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_83);
x_88 = l_Nat_repr(x_79);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_83);
x_91 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_92 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_83);
x_93 = l_Nat_repr(x_80);
x_94 = l_Lean_IR_VarId_HasToString___closed__1;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_83);
return x_97;
}
case 6:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
lean_dec(x_1);
x_100 = l_System_FilePath_dirName___closed__1;
x_101 = l_Lean_Name_toStringWithSep___main(x_100, x_98);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_box(0);
x_105 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_99, x_99, x_103, x_104);
lean_dec(x_99);
x_106 = 0;
x_107 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_106);
return x_107;
}
case 7:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
lean_dec(x_1);
x_110 = l_System_FilePath_dirName___closed__1;
x_111 = l_Lean_Name_toStringWithSep___main(x_110, x_108);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = 0;
x_114 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__22;
x_115 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_113);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_box(0);
x_118 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_109, x_109, x_116, x_117);
lean_dec(x_109);
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_113);
return x_119;
}
case 8:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 1);
lean_inc(x_121);
lean_dec(x_1);
x_122 = l_Nat_repr(x_120);
x_123 = l_Lean_IR_VarId_HasToString___closed__1;
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_125 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = 0;
x_127 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__24;
x_128 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set_uint8(x_128, sizeof(void*)*2, x_126);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_box(0);
x_131 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_121, x_121, x_129, x_130);
lean_dec(x_121);
x_132 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*2, x_126);
return x_132;
}
case 9:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
lean_dec(x_1);
x_134 = l_Nat_repr(x_133);
x_135 = l_Lean_IR_VarId_HasToString___closed__1;
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = 0;
x_139 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__26;
x_140 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_138);
return x_140;
}
case 10:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
lean_dec(x_1);
x_142 = l_Nat_repr(x_141);
x_143 = l_Lean_IR_VarId_HasToString___closed__1;
x_144 = lean_string_append(x_143, x_142);
lean_dec(x_142);
x_145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = 0;
x_147 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__28;
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_146);
return x_148;
}
case 11:
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_1, 0);
lean_inc(x_149);
lean_dec(x_1);
x_150 = l___private_Init_Lean_Compiler_IR_Format_2__formatLitVal(x_149);
return x_150;
}
case 12:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
lean_dec(x_1);
x_152 = l_Nat_repr(x_151);
x_153 = l_Lean_IR_VarId_HasToString___closed__1;
x_154 = lean_string_append(x_153, x_152);
lean_dec(x_152);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = 0;
x_157 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__30;
x_158 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_156);
return x_158;
}
default: 
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
lean_dec(x_1);
x_160 = l_Nat_repr(x_159);
x_161 = l_Lean_IR_VarId_HasToString___closed__1;
x_162 = lean_string_append(x_161, x_160);
lean_dec(x_160);
x_163 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = 0;
x_165 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr___closed__32;
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_164);
return x_166;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_7);
x_9 = 0;
lean_inc(x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_4, x_2);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_9);
return x_12;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Array_toList___rarg(x_11);
x_13 = l_Lean_formatKVMap___closed__1;
x_14 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_12, x_13);
lean_dec(x_12);
x_15 = 0;
x_16 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
x_18 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_15);
x_20 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_format_group(x_21);
x_23 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18;
x_24 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_15);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = l_Array_toList___rarg(x_25);
x_27 = l_Lean_formatKVMap___closed__1;
x_28 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_26, x_27);
lean_dec(x_26);
x_29 = 0;
x_30 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_31 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_29);
x_32 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_29);
x_34 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_format_group(x_35);
x_37 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23;
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_29);
return x_38;
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
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
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
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
x_12 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_9);
x_14 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_4);
lean_dec(x_4);
if (x_3 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Format_join___closed__1;
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_9);
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_9);
x_18 = l_Lean_Format_paren___closed__3;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__4;
x_21 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_9);
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_9);
x_23 = l_Lean_Format_paren___closed__3;
x_24 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_9);
return x_24;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_IR_formatAlt___closed__2;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_apply_1(x_1, x_5);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_10);
x_16 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_apply_1(x_1, x_18);
x_20 = 0;
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_20);
x_23 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_IR_formatAlt___closed__4;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_20);
return x_25;
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam(x_7);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__18;
x_3 = l_Lean_Format_join___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__20() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__19;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__22;
x_3 = l_Lean_Format_join___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__24() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_IR_formatFnBodyHead___closed__23;
x_3 = l_Lean_Format_flatten___main___closed__1;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
x_12 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_9);
x_14 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_3);
lean_dec(x_3);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_9);
x_16 = l_Lean_formatEntry___closed__2;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_9);
x_18 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(x_4);
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_9);
return x_19;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Nat_repr(x_20);
x_23 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_box(0);
x_28 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_21, x_21, x_26, x_27);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
x_31 = l_Lean_IR_formatFnBodyHead___closed__4;
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_29);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Nat_repr(x_33);
x_37 = l_Lean_IR_VarId_HasToString___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = 0;
x_41 = l_Lean_IR_formatFnBodyHead___closed__6;
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_40);
x_43 = l_Lean_Format_sbracket___closed__2;
x_44 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_40);
x_45 = l_Nat_repr(x_34);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_40);
x_48 = l_Lean_IR_formatFnBodyHead___closed__8;
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_40);
x_50 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_35);
x_51 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_40);
return x_51;
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Nat_repr(x_52);
x_55 = l_Lean_IR_VarId_HasToString___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = 0;
x_59 = l_Lean_IR_formatFnBodyHead___closed__10;
x_60 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_58);
x_61 = l_Lean_formatEntry___closed__2;
x_62 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_58);
x_63 = l_Nat_repr(x_53);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_58);
return x_65;
}
case 4:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
lean_dec(x_1);
x_69 = l_Nat_repr(x_66);
x_70 = l_Lean_IR_VarId_HasToString___closed__1;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = 0;
x_74 = l_Lean_IR_formatFnBodyHead___closed__12;
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_73);
x_76 = l_Lean_Format_sbracket___closed__2;
x_77 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_73);
x_78 = l_Nat_repr(x_67);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_73);
x_81 = l_Lean_IR_formatFnBodyHead___closed__8;
x_82 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_73);
x_83 = l_Nat_repr(x_68);
x_84 = lean_string_append(x_70, x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_73);
return x_86;
}
case 5:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 4);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Nat_repr(x_87);
x_93 = l_Lean_IR_VarId_HasToString___closed__1;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = 0;
x_97 = l_Lean_IR_formatFnBodyHead___closed__14;
x_98 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_96);
x_99 = l_Lean_Format_sbracket___closed__2;
x_100 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_96);
x_101 = l_Nat_repr(x_88);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_96);
x_104 = l_Lean_formatKVMap___closed__1;
x_105 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_96);
x_106 = l_Nat_repr(x_89);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_96);
x_109 = l_Lean_IR_formatFnBodyHead___closed__16;
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_96);
x_111 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_91);
lean_dec(x_91);
x_112 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*2, x_96);
x_113 = l_Lean_formatEntry___closed__2;
x_114 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_96);
x_115 = l_Nat_repr(x_90);
x_116 = lean_string_append(x_93, x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_96);
return x_118;
}
case 6:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_1, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_dec_eq(x_120, x_121);
x_123 = l_Nat_repr(x_119);
x_124 = l_Lean_IR_VarId_HasToString___closed__1;
x_125 = lean_string_append(x_124, x_123);
lean_dec(x_123);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (x_122 == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_127 = l_Nat_repr(x_120);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = 0;
x_130 = l_Lean_Format_sbracket___closed__2;
x_131 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_129);
x_132 = l_Lean_Format_sbracket___closed__3;
x_133 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_129);
x_134 = l_Lean_Format_sbracket___closed__1;
x_135 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_format_group(x_135);
x_137 = l_Lean_IR_formatFnBodyHead___closed__18;
x_138 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*2, x_129);
x_139 = l_Lean_Format_flatten___main___closed__1;
x_140 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_129);
x_141 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
lean_ctor_set_uint8(x_141, sizeof(void*)*2, x_129);
return x_141;
}
else
{
uint8_t x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_120);
x_142 = 0;
x_143 = l_Lean_IR_formatFnBodyHead___closed__20;
x_144 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_126);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_142);
return x_144;
}
}
case 7:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_1, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 1);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_dec_eq(x_146, x_147);
x_149 = l_Nat_repr(x_145);
x_150 = l_Lean_IR_VarId_HasToString___closed__1;
x_151 = lean_string_append(x_150, x_149);
lean_dec(x_149);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (x_148 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_153 = l_Nat_repr(x_146);
x_154 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = 0;
x_156 = l_Lean_Format_sbracket___closed__2;
x_157 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
lean_ctor_set_uint8(x_157, sizeof(void*)*2, x_155);
x_158 = l_Lean_Format_sbracket___closed__3;
x_159 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*2, x_155);
x_160 = l_Lean_Format_sbracket___closed__1;
x_161 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_format_group(x_161);
x_163 = l_Lean_IR_formatFnBodyHead___closed__22;
x_164 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_155);
x_165 = l_Lean_Format_flatten___main___closed__1;
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_155);
x_167 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_152);
lean_ctor_set_uint8(x_167, sizeof(void*)*2, x_155);
return x_167;
}
else
{
uint8_t x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_146);
x_168 = 0;
x_169 = l_Lean_IR_formatFnBodyHead___closed__24;
x_170 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_152);
lean_ctor_set_uint8(x_170, sizeof(void*)*2, x_168);
return x_170;
}
}
case 8:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
lean_dec(x_1);
x_172 = l_Nat_repr(x_171);
x_173 = l_Lean_IR_VarId_HasToString___closed__1;
x_174 = lean_string_append(x_173, x_172);
lean_dec(x_172);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = 0;
x_177 = l_Lean_IR_formatFnBodyHead___closed__26;
x_178 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set_uint8(x_178, sizeof(void*)*2, x_176);
return x_178;
}
case 9:
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_1, 0);
lean_inc(x_179);
lean_dec(x_1);
x_180 = l_Lean_formatKVMap(x_179);
x_181 = 0;
x_182 = l_Lean_IR_formatFnBodyHead___closed__28;
x_183 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_181);
return x_183;
}
case 10:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_1, 1);
lean_inc(x_184);
lean_dec(x_1);
x_185 = l_Nat_repr(x_184);
x_186 = l_Lean_IR_VarId_HasToString___closed__1;
x_187 = lean_string_append(x_186, x_185);
lean_dec(x_185);
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = 0;
x_190 = l_Lean_IR_formatFnBodyHead___closed__30;
x_191 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set_uint8(x_191, sizeof(void*)*2, x_189);
x_192 = l_Lean_IR_formatFnBodyHead___closed__32;
x_193 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set_uint8(x_193, sizeof(void*)*2, x_189);
return x_193;
}
case 11:
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_1, 0);
lean_inc(x_194);
lean_dec(x_1);
x_195 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_194);
x_196 = 0;
x_197 = l_Lean_IR_formatFnBodyHead___closed__34;
x_198 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_196);
return x_198;
}
case 12:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_1, 1);
lean_inc(x_200);
lean_dec(x_1);
x_201 = l_Nat_repr(x_199);
x_202 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_203 = lean_string_append(x_202, x_201);
lean_dec(x_201);
x_204 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = 0;
x_206 = l_Lean_IR_formatFnBodyHead___closed__36;
x_207 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
lean_ctor_set_uint8(x_207, sizeof(void*)*2, x_205);
x_208 = lean_unsigned_to_nat(0u);
x_209 = lean_box(0);
x_210 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_200, x_200, x_208, x_209);
lean_dec(x_200);
x_211 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set_uint8(x_211, sizeof(void*)*2, x_205);
return x_211;
}
default: 
{
lean_object* x_212; 
x_212 = l_Lean_IR_formatFnBodyHead___closed__38;
return x_212;
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_IR_formatFnBody___main), 2, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc(x_1);
x_13 = l_Lean_IR_formatAlt(x_12, x_1, x_8);
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_9);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_11);
x_14 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
x_16 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_4);
lean_dec(x_4);
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_11);
x_18 = l_Lean_formatEntry___closed__2;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_11);
x_20 = l___private_Init_Lean_Compiler_IR_Format_4__formatExpr(x_5);
x_21 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_11);
x_22 = l_Lean_IR_formatFnBody___main___closed__2;
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_11);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_11);
x_26 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_11);
return x_27;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Nat_repr(x_28);
x_33 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_box(0);
x_38 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_29, x_29, x_36, x_37);
lean_dec(x_29);
x_39 = 0;
x_40 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_39);
x_41 = l_Lean_IR_formatFnBody___main___closed__4;
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_39);
lean_inc(x_1);
x_43 = l_Lean_IR_formatFnBody___main(x_1, x_30);
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_39);
lean_inc(x_1);
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_39);
x_48 = l_Lean_IR_formatFnBody___main___closed__2;
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_39);
x_50 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_39);
x_51 = l_Lean_IR_formatFnBody___main(x_1, x_31);
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_39);
return x_52;
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 3);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Nat_repr(x_53);
x_58 = l_Lean_IR_VarId_HasToString___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = 0;
x_62 = l_Lean_IR_formatFnBodyHead___closed__6;
x_63 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_61);
x_64 = l_Lean_Format_sbracket___closed__2;
x_65 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_61);
x_66 = l_Nat_repr(x_54);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_61);
x_69 = l_Lean_IR_formatFnBodyHead___closed__8;
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_61);
x_71 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_55);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_61);
x_73 = l_Lean_IR_formatFnBody___main___closed__2;
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_61);
x_75 = lean_box(1);
x_76 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_61);
x_77 = l_Lean_IR_formatFnBody___main(x_1, x_56);
x_78 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_61);
return x_78;
}
case 3:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
lean_dec(x_2);
x_82 = l_Nat_repr(x_79);
x_83 = l_Lean_IR_VarId_HasToString___closed__1;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = 0;
x_87 = l_Lean_IR_formatFnBodyHead___closed__10;
x_88 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_86);
x_89 = l_Lean_formatEntry___closed__2;
x_90 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_86);
x_91 = l_Nat_repr(x_80);
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_86);
x_94 = l_Lean_IR_formatFnBody___main___closed__2;
x_95 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_86);
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_86);
x_98 = l_Lean_IR_formatFnBody___main(x_1, x_81);
x_99 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_86);
return x_99;
}
case 4:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_100 = lean_ctor_get(x_2, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_2, 3);
lean_inc(x_103);
lean_dec(x_2);
x_104 = l_Nat_repr(x_100);
x_105 = l_Lean_IR_VarId_HasToString___closed__1;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = 0;
x_109 = l_Lean_IR_formatFnBodyHead___closed__12;
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_108);
x_111 = l_Lean_Format_sbracket___closed__2;
x_112 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*2, x_108);
x_113 = l_Nat_repr(x_101);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_108);
x_116 = l_Lean_IR_formatFnBodyHead___closed__8;
x_117 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_108);
x_118 = l_Nat_repr(x_102);
x_119 = lean_string_append(x_105, x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_108);
x_122 = l_Lean_IR_formatFnBody___main___closed__2;
x_123 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_108);
x_124 = lean_box(1);
x_125 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_108);
x_126 = l_Lean_IR_formatFnBody___main(x_1, x_103);
x_127 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_108);
return x_127;
}
case 5:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_128 = lean_ctor_get(x_2, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_2, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_2, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_2, 5);
lean_inc(x_133);
lean_dec(x_2);
x_134 = l_Nat_repr(x_128);
x_135 = l_Lean_IR_VarId_HasToString___closed__1;
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = 0;
x_139 = l_Lean_IR_formatFnBodyHead___closed__14;
x_140 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_138);
x_141 = l_Lean_Format_sbracket___closed__2;
x_142 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_138);
x_143 = l_Nat_repr(x_129);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_138);
x_146 = l_Lean_formatKVMap___closed__1;
x_147 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_138);
x_148 = l_Nat_repr(x_130);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_138);
x_151 = l_Lean_IR_formatFnBodyHead___closed__16;
x_152 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*2, x_138);
x_153 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_132);
lean_dec(x_132);
x_154 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_138);
x_155 = l_Lean_formatEntry___closed__2;
x_156 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_138);
x_157 = l_Nat_repr(x_131);
x_158 = lean_string_append(x_135, x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_138);
x_161 = l_Lean_IR_formatFnBody___main___closed__2;
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_138);
x_163 = lean_box(1);
x_164 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_138);
x_165 = l_Lean_IR_formatFnBody___main(x_1, x_133);
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_138);
return x_166;
}
case 6:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_2, 2);
lean_inc(x_169);
lean_dec(x_2);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_dec_eq(x_168, x_170);
x_172 = l_Nat_repr(x_167);
x_173 = l_Lean_IR_VarId_HasToString___closed__1;
x_174 = lean_string_append(x_173, x_172);
lean_dec(x_172);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = l_Lean_IR_formatFnBody___main(x_1, x_169);
if (x_171 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_177 = l_Nat_repr(x_168);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = 0;
x_180 = l_Lean_Format_sbracket___closed__2;
x_181 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set_uint8(x_181, sizeof(void*)*2, x_179);
x_182 = l_Lean_Format_sbracket___closed__3;
x_183 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_179);
x_184 = l_Lean_Format_sbracket___closed__1;
x_185 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_format_group(x_185);
x_187 = l_Lean_IR_formatFnBodyHead___closed__18;
x_188 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*2, x_179);
x_189 = l_Lean_Format_flatten___main___closed__1;
x_190 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*2, x_179);
x_191 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_175);
lean_ctor_set_uint8(x_191, sizeof(void*)*2, x_179);
x_192 = l_Lean_IR_formatFnBody___main___closed__2;
x_193 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set_uint8(x_193, sizeof(void*)*2, x_179);
x_194 = lean_box(1);
x_195 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*2, x_179);
x_196 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_176);
lean_ctor_set_uint8(x_196, sizeof(void*)*2, x_179);
return x_196;
}
else
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_168);
x_197 = 0;
x_198 = l_Lean_IR_formatFnBodyHead___closed__20;
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_175);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_197);
x_200 = l_Lean_IR_formatFnBody___main___closed__2;
x_201 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_197);
x_202 = lean_box(1);
x_203 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*2, x_197);
x_204 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_176);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_197);
return x_204;
}
}
case 7:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_205 = lean_ctor_get(x_2, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_2, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_2, 2);
lean_inc(x_207);
lean_dec(x_2);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_dec_eq(x_206, x_208);
x_210 = l_Nat_repr(x_205);
x_211 = l_Lean_IR_VarId_HasToString___closed__1;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = l_Lean_IR_formatFnBody___main(x_1, x_207);
if (x_209 == 0)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_215 = l_Nat_repr(x_206);
x_216 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = 0;
x_218 = l_Lean_Format_sbracket___closed__2;
x_219 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set_uint8(x_219, sizeof(void*)*2, x_217);
x_220 = l_Lean_Format_sbracket___closed__3;
x_221 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set_uint8(x_221, sizeof(void*)*2, x_217);
x_222 = l_Lean_Format_sbracket___closed__1;
x_223 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = lean_format_group(x_223);
x_225 = l_Lean_IR_formatFnBodyHead___closed__22;
x_226 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_217);
x_227 = l_Lean_Format_flatten___main___closed__1;
x_228 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*2, x_217);
x_229 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_213);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_217);
x_230 = l_Lean_IR_formatFnBody___main___closed__2;
x_231 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
lean_ctor_set_uint8(x_231, sizeof(void*)*2, x_217);
x_232 = lean_box(1);
x_233 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_217);
x_234 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_214);
lean_ctor_set_uint8(x_234, sizeof(void*)*2, x_217);
return x_234;
}
else
{
uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_206);
x_235 = 0;
x_236 = l_Lean_IR_formatFnBodyHead___closed__24;
x_237 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_213);
lean_ctor_set_uint8(x_237, sizeof(void*)*2, x_235);
x_238 = l_Lean_IR_formatFnBody___main___closed__2;
x_239 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*2, x_235);
x_240 = lean_box(1);
x_241 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set_uint8(x_241, sizeof(void*)*2, x_235);
x_242 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_214);
lean_ctor_set_uint8(x_242, sizeof(void*)*2, x_235);
return x_242;
}
}
case 8:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_243 = lean_ctor_get(x_2, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_2, 1);
lean_inc(x_244);
lean_dec(x_2);
x_245 = l_Nat_repr(x_243);
x_246 = l_Lean_IR_VarId_HasToString___closed__1;
x_247 = lean_string_append(x_246, x_245);
lean_dec(x_245);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = 0;
x_250 = l_Lean_IR_formatFnBodyHead___closed__26;
x_251 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set_uint8(x_251, sizeof(void*)*2, x_249);
x_252 = l_Lean_IR_formatFnBody___main___closed__2;
x_253 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set_uint8(x_253, sizeof(void*)*2, x_249);
x_254 = lean_box(1);
x_255 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set_uint8(x_255, sizeof(void*)*2, x_249);
x_256 = l_Lean_IR_formatFnBody___main(x_1, x_244);
x_257 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set_uint8(x_257, sizeof(void*)*2, x_249);
return x_257;
}
case 9:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_258 = lean_ctor_get(x_2, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_2, 1);
lean_inc(x_259);
lean_dec(x_2);
x_260 = l_Lean_formatKVMap(x_258);
x_261 = 0;
x_262 = l_Lean_IR_formatFnBodyHead___closed__28;
x_263 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
lean_ctor_set_uint8(x_263, sizeof(void*)*2, x_261);
x_264 = l_Lean_IR_formatFnBody___main___closed__2;
x_265 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set_uint8(x_265, sizeof(void*)*2, x_261);
x_266 = lean_box(1);
x_267 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*2, x_261);
x_268 = l_Lean_IR_formatFnBody___main(x_1, x_259);
x_269 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_261);
return x_269;
}
case 10:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_270 = lean_ctor_get(x_2, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_2, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_2, 3);
lean_inc(x_272);
lean_dec(x_2);
x_273 = l_Nat_repr(x_270);
x_274 = l_Lean_IR_VarId_HasToString___closed__1;
x_275 = lean_string_append(x_274, x_273);
lean_dec(x_273);
x_276 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_276, 0, x_275);
x_277 = 0;
x_278 = l_Lean_IR_formatFnBodyHead___closed__30;
x_279 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set_uint8(x_279, sizeof(void*)*2, x_277);
x_280 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_281 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set_uint8(x_281, sizeof(void*)*2, x_277);
x_282 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_271);
lean_dec(x_271);
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_277);
x_284 = l_Lean_IR_formatFnBody___main___closed__6;
x_285 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*2, x_277);
x_286 = lean_unsigned_to_nat(0u);
x_287 = lean_box(0);
x_288 = l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_272, x_272, x_286, x_287);
lean_dec(x_272);
x_289 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*2, x_277);
return x_289;
}
case 11:
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_1);
x_290 = lean_ctor_get(x_2, 0);
lean_inc(x_290);
lean_dec(x_2);
x_291 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg(x_290);
x_292 = 0;
x_293 = l_Lean_IR_formatFnBodyHead___closed__34;
x_294 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_292);
return x_294;
}
case 12:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_1);
x_295 = lean_ctor_get(x_2, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_2, 1);
lean_inc(x_296);
lean_dec(x_2);
x_297 = l_Nat_repr(x_295);
x_298 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_299 = lean_string_append(x_298, x_297);
lean_dec(x_297);
x_300 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_300, 0, x_299);
x_301 = 0;
x_302 = l_Lean_IR_formatFnBodyHead___closed__36;
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_301);
x_304 = lean_unsigned_to_nat(0u);
x_305 = lean_box(0);
x_306 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_296, x_296, x_304, x_305);
lean_dec(x_296);
x_307 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_306);
lean_ctor_set_uint8(x_307, sizeof(void*)*2, x_301);
return x_307;
}
default: 
{
lean_object* x_308; 
lean_dec(x_1);
x_308 = l_Lean_IR_formatFnBodyHead___closed__38;
return x_308;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_3);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_IR_formatDecl___closed__2;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_box(0);
x_15 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_13, x_14);
lean_dec(x_4);
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_10);
x_17 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_18 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_10);
x_19 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_5);
lean_dec(x_5);
x_20 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_10);
x_21 = l_Lean_IR_formatFnBody___main___closed__4;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_10);
lean_inc(x_1);
x_23 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_10);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_28);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = 0;
x_35 = l_Lean_IR_formatDecl___closed__4;
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_box(0);
x_39 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_29, x_29, x_37, x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_34);
x_41 = l___private_Init_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_34);
x_43 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_30);
lean_dec(x_30);
x_44 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_34);
return x_44;
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
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Format(lean_io_mk_world());
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
