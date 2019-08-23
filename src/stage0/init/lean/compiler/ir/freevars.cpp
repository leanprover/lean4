// Lean compiler output
// Module: init.lean.compiler.ir.freevars
// Imports: init.lean.compiler.ir.basic
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
uint8 l_Lean_IR_Arg_hasFreeVar(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_3__collectVar___boxed(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_1__skip___boxed(obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_13__skip___boxed(obj*);
obj* l___private_init_lean_compiler_ir_freevars_26__collectAlts___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__1(obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_10__collectParams(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitParams(obj*, obj*);
obj* l_Lean_IR_MaxIndex_HasAndthen;
obj* l_Lean_IR_Arg_hasFreeVar___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1(obj*);
obj* l_Lean_IR_FnBody_maxIndex(obj*);
obj* l___private_init_lean_compiler_ir_freevars_11__collectExpr(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_freeIndices(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectFnBody___main___closed__1;
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_6__collectArg___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1(obj*);
obj* l___private_init_lean_compiler_ir_freevars_14__collectIndex(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_19__withJP(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_4__collectJP___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_22__collectArg___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FreeIndices_collectFnBody(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_26__collectAlts(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_4__collectJP(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_25__collectExpr___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_2__collect(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__1(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_10__collectParams___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_HasIndex_visitVar___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_16__collectJP___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body(obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_3__collectVar(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FreeIndices_collectFnBody___main___closed__1;
obj* l_Lean_IR_MaxIndex_collectFnBody(obj*, obj*);
uint8 l_Lean_IR_Expr_hasFreeVar(obj*, obj*);
obj* l_Lean_IR_FreeIndices_HasAndthen;
obj* l_Lean_IR_Expr_hasFreeVar___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_16__collectJP(obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitArgs(obj*, obj*);
extern "C" uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Lean_IR_FreeIndices_insertParams___boxed(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitParams___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_nat_add(obj*, obj*);
obj* l_Lean_IR_MaxIndex_HasAndthen___closed__1;
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___rarg(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_nat_dec_eq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_13__skip___rarg(obj*);
obj* l___private_init_lean_compiler_ir_freevars_12__collectAlts___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_20__withParams___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FreeIndices_collectFnBody___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_22__collectArg(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_24__collectArgs___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_collectFreeIndices(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_15__collectVar___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_13__skip___rarg___boxed(obj*);
obj* l___private_init_lean_compiler_ir_freevars_8__collectArgs___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitParams___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_hasFreeVar___boxed(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitJP___boxed(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitVar(obj*, obj*);
uint8 l_Lean_IR_FnBody_hasFreeVar(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_HasIndex_visitExpr___boxed(obj*, obj*);
obj* l_Lean_IR_Decl_maxIndex(obj*);
obj* l_Lean_IR_FreeIndices_HasAndthen___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_HasIndex_visitArgs___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_8__collectArgs(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_2__collect___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_14__collectIndex___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_18__withVar(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_5__seq(obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitExpr(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_HasIndex_visitFnBody___main___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_6__collectArg(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_9__collectParam(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_9__collectParam___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_24__collectArgs(obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_13__skip(obj*);
obj* l___private_init_lean_compiler_ir_freevars_20__withParams(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitJP(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_21__seq(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectFnBody___main(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitArg(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray(obj*);
obj* l___private_init_lean_compiler_ir_freevars_17__withIndex(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_12__collectAlts(obj*, obj*, obj*);
obj* l_Lean_IR_HasIndex_visitArg___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_25__collectExpr(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_1__skip(obj*);
obj* l___private_init_lean_compiler_ir_freevars_15__collectVar(obj*, obj*, obj*);
obj* l_Lean_IR_FreeIndices_insertParams(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitFnBody___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_freevars_1__skip(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_freevars_1__skip___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_freevars_1__skip(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_freevars_2__collect(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_2__collect___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_2__collect(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_3__collectVar(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_3__collectVar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_3__collectVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_4__collectJP(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_4__collectJP___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_4__collectJP(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_5__seq(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_IR_MaxIndex_HasAndthen___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_freevars_5__seq), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_IR_MaxIndex_HasAndthen() {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_MaxIndex_HasAndthen___closed__1;
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_freevars_6__collectArg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_3);
return x_3;
}
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_6__collectArg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_6__collectArg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean::inc(x_2);
x_9 = lean::apply_2(x_2, x_8, x_5);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg(x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_freevars_7__collectArray___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_7__collectArray___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_7__collectArray___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l___private_init_lean_compiler_ir_freevars_6__collectArg(x_7, x_4);
lean::dec(x_4);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_8__collectArgs(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_8__collectArgs___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_8__collectArgs(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_9__collectParam(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_3);
return x_3;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_9__collectParam___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_9__collectParam(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l___private_init_lean_compiler_ir_freevars_9__collectParam(x_7, x_4);
lean::dec(x_4);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_10__collectParams(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_10__collectParams___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_freevars_10__collectParams(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_11__collectExpr(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_3, x_3, x_4, x_2);
lean::dec(x_3);
return x_5;
}
case 1:
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
if (x_7 == 0)
{
lean::dec(x_6);
return x_2;
}
else
{
lean::dec(x_2);
return x_6;
}
}
case 2:
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean_nat_dec_lt(x_2, x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_8);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_9, x_9, x_11, x_2);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_2);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_9, x_9, x_13, x_8);
lean::dec(x_9);
return x_14;
}
}
case 3:
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::dec(x_1);
x_16 = lean_nat_dec_lt(x_2, x_15);
if (x_16 == 0)
{
lean::dec(x_15);
return x_2;
}
else
{
lean::dec(x_2);
return x_15;
}
}
case 4:
{
obj* x_17; uint8 x_18; 
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::dec(x_1);
x_18 = lean_nat_dec_lt(x_2, x_17);
if (x_18 == 0)
{
lean::dec(x_17);
return x_2;
}
else
{
lean::dec(x_2);
return x_17;
}
}
case 5:
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
lean::dec(x_1);
x_20 = lean_nat_dec_lt(x_2, x_19);
if (x_20 == 0)
{
lean::dec(x_19);
return x_2;
}
else
{
lean::dec(x_2);
return x_19;
}
}
case 6:
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
lean::dec(x_1);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_21, x_21, x_22, x_2);
lean::dec(x_21);
return x_23;
}
case 7:
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_1, 1);
lean::inc(x_24);
lean::dec(x_1);
x_25 = lean::mk_nat_obj(0u);
x_26 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_24, x_24, x_25, x_2);
lean::dec(x_24);
return x_26;
}
case 8:
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_1, 1);
lean::inc(x_28);
lean::dec(x_1);
x_29 = lean_nat_dec_lt(x_2, x_27);
if (x_29 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_27);
x_30 = lean::mk_nat_obj(0u);
x_31 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_28, x_28, x_30, x_2);
lean::dec(x_28);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_2);
x_32 = lean::mk_nat_obj(0u);
x_33 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_28, x_28, x_32, x_27);
lean::dec(x_28);
return x_33;
}
}
case 11:
{
lean::dec(x_1);
return x_2;
}
default: 
{
obj* x_34; uint8 x_35; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
lean::dec(x_1);
x_35 = lean_nat_dec_lt(x_2, x_34);
if (x_35 == 0)
{
lean::dec(x_34);
return x_2;
}
else
{
lean::dec(x_2);
return x_34;
}
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean::dec(x_8);
lean::inc(x_1);
x_10 = lean::apply_2(x_1, x_9, x_5);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(x_1, x_2, x_2, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_12__collectAlts(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(x_1, x_2, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_7__collectArray___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_12__collectAlts___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_12__collectAlts(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_MaxIndex_collectFnBody___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_MaxIndex_collectFnBody___main), 2, 0);
return x_1;
}
}
obj* l_Lean_IR_MaxIndex_collectFnBody___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l___private_init_lean_compiler_ir_freevars_11__collectExpr(x_3, x_2);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
case 1:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::dec(x_1);
x_10 = l_Lean_IR_MaxIndex_collectFnBody___main(x_8, x_2);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(x_7, x_7, x_11, x_10);
lean::dec(x_7);
x_1 = x_9;
x_2 = x_12;
goto _start;
}
case 2:
{
obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_1, 2);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
lean::dec(x_1);
x_17 = lean_nat_dec_lt(x_2, x_14);
if (x_17 == 0)
{
obj* x_18; 
lean::dec(x_14);
x_18 = l___private_init_lean_compiler_ir_freevars_6__collectArg(x_15, x_2);
lean::dec(x_2);
lean::dec(x_15);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
else
{
obj* x_20; 
lean::dec(x_2);
x_20 = l___private_init_lean_compiler_ir_freevars_6__collectArg(x_15, x_14);
lean::dec(x_14);
lean::dec(x_15);
x_1 = x_16;
x_2 = x_20;
goto _start;
}
}
case 4:
{
obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_1, 2);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_1, 3);
lean::inc(x_24);
lean::dec(x_1);
x_25 = lean_nat_dec_lt(x_2, x_22);
if (x_25 == 0)
{
uint8 x_26; 
lean::dec(x_22);
x_26 = lean_nat_dec_lt(x_2, x_23);
if (x_26 == 0)
{
lean::dec(x_23);
x_1 = x_24;
goto _start;
}
else
{
lean::dec(x_2);
x_1 = x_24;
x_2 = x_23;
goto _start;
}
}
else
{
uint8 x_29; 
lean::dec(x_2);
x_29 = lean_nat_dec_lt(x_22, x_23);
if (x_29 == 0)
{
lean::dec(x_23);
x_1 = x_24;
x_2 = x_22;
goto _start;
}
else
{
lean::dec(x_22);
x_1 = x_24;
x_2 = x_23;
goto _start;
}
}
}
case 5:
{
obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_1, 3);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_1, 4);
lean::inc(x_34);
lean::dec(x_1);
x_35 = lean_nat_dec_lt(x_2, x_32);
if (x_35 == 0)
{
uint8 x_36; 
lean::dec(x_32);
x_36 = lean_nat_dec_lt(x_2, x_33);
if (x_36 == 0)
{
lean::dec(x_33);
x_1 = x_34;
goto _start;
}
else
{
lean::dec(x_2);
x_1 = x_34;
x_2 = x_33;
goto _start;
}
}
else
{
uint8 x_39; 
lean::dec(x_2);
x_39 = lean_nat_dec_lt(x_32, x_33);
if (x_39 == 0)
{
lean::dec(x_33);
x_1 = x_34;
x_2 = x_32;
goto _start;
}
else
{
lean::dec(x_32);
x_1 = x_34;
x_2 = x_33;
goto _start;
}
}
}
case 8:
{
obj* x_42; obj* x_43; uint8 x_44; 
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
lean::dec(x_1);
x_44 = lean_nat_dec_lt(x_2, x_42);
if (x_44 == 0)
{
lean::dec(x_42);
x_1 = x_43;
goto _start;
}
else
{
lean::dec(x_2);
x_1 = x_43;
x_2 = x_42;
goto _start;
}
}
case 9:
{
obj* x_47; 
x_47 = lean::cnstr_get(x_1, 1);
lean::inc(x_47);
lean::dec(x_1);
x_1 = x_47;
goto _start;
}
case 10:
{
obj* x_49; obj* x_50; uint8 x_51; 
x_49 = lean::cnstr_get(x_1, 1);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_1, 2);
lean::inc(x_50);
lean::dec(x_1);
x_51 = lean_nat_dec_lt(x_2, x_49);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_49);
x_52 = l_Lean_IR_MaxIndex_collectFnBody___main___closed__1;
x_53 = lean::mk_nat_obj(0u);
x_54 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(x_52, x_50, x_50, x_53, x_2);
lean::dec(x_50);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_2);
x_55 = l_Lean_IR_MaxIndex_collectFnBody___main___closed__1;
x_56 = lean::mk_nat_obj(0u);
x_57 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_12__collectAlts___spec__2(x_55, x_50, x_50, x_56, x_49);
lean::dec(x_50);
return x_57;
}
}
case 11:
{
obj* x_58; obj* x_59; 
x_58 = lean::cnstr_get(x_1, 0);
lean::inc(x_58);
lean::dec(x_1);
x_59 = l___private_init_lean_compiler_ir_freevars_6__collectArg(x_58, x_2);
lean::dec(x_2);
lean::dec(x_58);
return x_59;
}
case 12:
{
obj* x_60; obj* x_61; uint8 x_62; 
x_60 = lean::cnstr_get(x_1, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_1, 1);
lean::inc(x_61);
lean::dec(x_1);
x_62 = lean_nat_dec_lt(x_2, x_60);
if (x_62 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_60);
x_63 = lean::mk_nat_obj(0u);
x_64 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_61, x_61, x_63, x_2);
lean::dec(x_61);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_2);
x_65 = lean::mk_nat_obj(0u);
x_66 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_8__collectArgs___spec__2(x_61, x_61, x_65, x_60);
lean::dec(x_61);
return x_66;
}
}
case 13:
{
return x_2;
}
default: 
{
obj* x_67; obj* x_68; uint8 x_69; 
x_67 = lean::cnstr_get(x_1, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_1, 2);
lean::inc(x_68);
lean::dec(x_1);
x_69 = lean_nat_dec_lt(x_2, x_67);
if (x_69 == 0)
{
lean::dec(x_67);
x_1 = x_68;
goto _start;
}
else
{
lean::dec(x_2);
x_1 = x_68;
x_2 = x_67;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_MaxIndex_collectFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MaxIndex_collectFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_MaxIndex_collectDecl(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(x_3, x_3, x_5, x_2);
lean::dec(x_3);
x_7 = l_Lean_IR_MaxIndex_collectFnBody___main(x_4, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_10__collectParams___spec__2(x_8, x_8, x_9, x_2);
lean::dec(x_8);
return x_10;
}
}
}
obj* l_Lean_IR_FnBody_maxIndex(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_IR_MaxIndex_collectFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Decl_maxIndex(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_13__skip___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_freevars_13__skip(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_freevars_13__skip___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_freevars_13__skip___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_freevars_13__skip___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_freevars_13__skip___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_freevars_13__skip(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean_nat_dec_lt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::inc(x_6);
lean::inc(x_5);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_6);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_14__collectIndex(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
return x_6;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
}
}
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_14__collectIndex___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_14__collectIndex(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_15__collectVar(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
return x_6;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_15__collectVar___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_15__collectVar(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_16__collectJP(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
return x_6;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_16__collectJP___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_16__collectJP(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_17__withIndex(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
x_7 = lean::apply_2(x_2, x_6, x_4);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_freevars_18__withVar(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
x_7 = lean::apply_2(x_2, x_6, x_4);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_freevars_19__withJP(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
x_7 = lean::apply_2(x_2, x_6, x_4);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_3, x_9);
lean::dec(x_3);
x_11 = lean::box(0);
x_12 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_8, x_11);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
}
}
obj* l_Lean_IR_FreeIndices_insertParams(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1(x_2, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_FreeIndices_insertParams___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_FreeIndices_insertParams(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_freevars_20__withParams(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1(x_1, x_1, x_5, x_3);
x_7 = lean::apply_2(x_2, x_6, x_4);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_freevars_20__withParams___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_freevars_20__withParams(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_21__seq(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
x_5 = lean::apply_2(x_1, x_3, x_4);
x_6 = lean::apply_2(x_2, x_3, x_5);
return x_6;
}
}
obj* _init_l_Lean_IR_FreeIndices_HasAndthen___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_freevars_21__seq), 4, 0);
return x_1;
}
}
obj* _init_l_Lean_IR_FreeIndices_HasAndthen() {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FreeIndices_HasAndthen___closed__1;
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_freevars_22__collectArg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::box(0);
x_7 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_4, x_6);
return x_7;
}
else
{
lean::dec(x_5);
lean::dec(x_4);
return x_3;
}
}
else
{
return x_3;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_22__collectArg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_22__collectArg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean_array_fget(x_4, x_5);
lean::inc(x_2);
lean::inc(x_3);
x_10 = lean::apply_3(x_2, x_9, x_3, x_6);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_5, x_11);
lean::dec(x_5);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg(x_1, x_2, x_3, x_1, x_5, x_4);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_freevars_23__collectArray___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_23__collectArray___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_1);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_freevars_23__collectArray___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l___private_init_lean_compiler_ir_freevars_22__collectArg(x_8, x_2, x_5);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_24__collectArgs(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_24__collectArgs___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_24__collectArgs(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_freevars_25__collectExpr(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_4, x_2, x_4, x_5, x_3);
lean::dec(x_4);
return x_6;
}
case 1:
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::box(0);
x_10 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_7, x_9);
return x_10;
}
else
{
lean::dec(x_8);
lean::dec(x_7);
return x_3;
}
}
case 2:
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
x_13 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::box(0);
x_15 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_11, x_14);
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_12, x_2, x_12, x_16, x_15);
lean::dec(x_12);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_13);
lean::dec(x_11);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_12, x_2, x_12, x_18, x_3);
lean::dec(x_12);
return x_19;
}
}
case 3:
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
lean::dec(x_1);
x_21 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::box(0);
x_23 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_20, x_22);
return x_23;
}
else
{
lean::dec(x_21);
lean::dec(x_20);
return x_3;
}
}
case 4:
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_1, 1);
lean::inc(x_24);
lean::dec(x_1);
x_25 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::box(0);
x_27 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_24, x_26);
return x_27;
}
else
{
lean::dec(x_25);
lean::dec(x_24);
return x_3;
}
}
case 5:
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_1, 2);
lean::inc(x_28);
lean::dec(x_1);
x_29 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; 
x_30 = lean::box(0);
x_31 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_28, x_30);
return x_31;
}
else
{
lean::dec(x_29);
lean::dec(x_28);
return x_3;
}
}
case 6:
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_1, 1);
lean::inc(x_32);
lean::dec(x_1);
x_33 = lean::mk_nat_obj(0u);
x_34 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_32, x_2, x_32, x_33, x_3);
lean::dec(x_32);
return x_34;
}
case 7:
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_1, 1);
lean::inc(x_35);
lean::dec(x_1);
x_36 = lean::mk_nat_obj(0u);
x_37 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_35, x_2, x_35, x_36, x_3);
lean::dec(x_35);
return x_37;
}
case 8:
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_1, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_1, 1);
lean::inc(x_39);
lean::dec(x_1);
x_40 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_38);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = lean::box(0);
x_42 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_38, x_41);
x_43 = lean::mk_nat_obj(0u);
x_44 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_39, x_2, x_39, x_43, x_42);
lean::dec(x_39);
return x_44;
}
else
{
obj* x_45; obj* x_46; 
lean::dec(x_40);
lean::dec(x_38);
x_45 = lean::mk_nat_obj(0u);
x_46 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_39, x_2, x_39, x_45, x_3);
lean::dec(x_39);
return x_46;
}
}
case 11:
{
lean::dec(x_1);
return x_3;
}
default: 
{
obj* x_47; obj* x_48; 
x_47 = lean::cnstr_get(x_1, 0);
lean::inc(x_47);
lean::dec(x_1);
x_48 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::box(0);
x_50 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_47, x_49);
return x_50;
}
else
{
lean::dec(x_48);
lean::dec(x_47);
return x_3;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_25__collectExpr___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_freevars_25__collectExpr(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = l_Lean_IR_AltCore_body(x_9);
lean::dec(x_9);
lean::inc(x_1);
lean::inc(x_3);
x_11 = lean::apply_3(x_1, x_10, x_3, x_6);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_5, x_12);
lean::dec(x_5);
x_5 = x_13;
x_6 = x_11;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(x_1, x_2, x_3, x_2, x_5, x_4);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_freevars_26__collectAlts(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(x_1, x_2, x_3, x_2, x_5, x_4);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_2);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_freevars_23__collectArray___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_freevars_26__collectAlts___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_freevars_26__collectAlts(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_IR_FreeIndices_collectFnBody___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_FreeIndices_collectFnBody___main), 3, 0);
return x_1;
}
}
obj* l_Lean_IR_FreeIndices_collectFnBody___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_7 = l___private_init_lean_compiler_ir_freevars_25__collectExpr(x_5, x_2, x_3);
x_8 = lean::box(0);
x_9 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_4, x_8);
x_1 = x_6;
x_2 = x_9;
x_3 = x_7;
goto _start;
}
case 1:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_1, 2);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_1, 3);
lean::inc(x_14);
lean::dec(x_1);
x_15 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_16 = l_Array_miterateAux___main___at_Lean_IR_FreeIndices_insertParams___spec__1(x_12, x_12, x_15, x_2);
lean::dec(x_12);
x_17 = l_Lean_IR_FreeIndices_collectFnBody___main(x_13, x_16, x_3);
x_18 = lean::box(0);
x_19 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_11, x_18);
x_1 = x_14;
x_2 = x_19;
x_3 = x_17;
goto _start;
}
case 2:
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_1, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_1, 2);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_23);
lean::dec(x_1);
x_24 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_21);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::box(0);
x_26 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_21, x_25);
x_27 = l___private_init_lean_compiler_ir_freevars_22__collectArg(x_22, x_2, x_26);
x_1 = x_23;
x_3 = x_27;
goto _start;
}
else
{
obj* x_29; 
lean::dec(x_24);
lean::dec(x_21);
x_29 = l___private_init_lean_compiler_ir_freevars_22__collectArg(x_22, x_2, x_3);
x_1 = x_23;
x_3 = x_29;
goto _start;
}
}
case 4:
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_1, 2);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_1, 3);
lean::inc(x_33);
lean::dec(x_1);
x_34 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_31);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::box(0);
x_36 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_31, x_35);
x_37 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_32);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_36, x_32, x_35);
x_1 = x_33;
x_3 = x_38;
goto _start;
}
else
{
lean::dec(x_37);
lean::dec(x_32);
x_1 = x_33;
x_3 = x_36;
goto _start;
}
}
else
{
obj* x_41; 
lean::dec(x_34);
lean::dec(x_31);
x_41 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_32);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::box(0);
x_43 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_32, x_42);
x_1 = x_33;
x_3 = x_43;
goto _start;
}
else
{
lean::dec(x_41);
lean::dec(x_32);
x_1 = x_33;
goto _start;
}
}
}
case 5:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_46 = lean::cnstr_get(x_1, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_1, 3);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_1, 4);
lean::inc(x_48);
lean::dec(x_1);
x_49 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_46);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::box(0);
x_51 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_46, x_50);
x_52 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_47);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; 
x_53 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_51, x_47, x_50);
x_1 = x_48;
x_3 = x_53;
goto _start;
}
else
{
lean::dec(x_52);
lean::dec(x_47);
x_1 = x_48;
x_3 = x_51;
goto _start;
}
}
else
{
obj* x_56; 
lean::dec(x_49);
lean::dec(x_46);
x_56 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_47);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; 
x_57 = lean::box(0);
x_58 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_47, x_57);
x_1 = x_48;
x_3 = x_58;
goto _start;
}
else
{
lean::dec(x_56);
lean::dec(x_47);
x_1 = x_48;
goto _start;
}
}
}
case 8:
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = lean::cnstr_get(x_1, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_1, 1);
lean::inc(x_62);
lean::dec(x_1);
x_63 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_61);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; 
x_64 = lean::box(0);
x_65 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_61, x_64);
x_1 = x_62;
x_3 = x_65;
goto _start;
}
else
{
lean::dec(x_63);
lean::dec(x_61);
x_1 = x_62;
goto _start;
}
}
case 9:
{
obj* x_68; 
x_68 = lean::cnstr_get(x_1, 1);
lean::inc(x_68);
lean::dec(x_1);
x_1 = x_68;
goto _start;
}
case 10:
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_1, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_1, 2);
lean::inc(x_71);
lean::dec(x_1);
x_72 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_70);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::box(0);
x_74 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_70, x_73);
x_75 = l_Lean_IR_FreeIndices_collectFnBody___main___closed__1;
x_76 = lean::mk_nat_obj(0u);
x_77 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(x_75, x_71, x_2, x_71, x_76, x_74);
lean::dec(x_71);
return x_77;
}
else
{
obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_72);
lean::dec(x_70);
x_78 = l_Lean_IR_FreeIndices_collectFnBody___main___closed__1;
x_79 = lean::mk_nat_obj(0u);
x_80 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_26__collectAlts___spec__2(x_78, x_71, x_2, x_71, x_79, x_3);
lean::dec(x_71);
return x_80;
}
}
case 11:
{
obj* x_81; obj* x_82; 
x_81 = lean::cnstr_get(x_1, 0);
lean::inc(x_81);
lean::dec(x_1);
x_82 = l___private_init_lean_compiler_ir_freevars_22__collectArg(x_81, x_2, x_3);
lean::dec(x_2);
return x_82;
}
case 12:
{
obj* x_83; obj* x_84; obj* x_85; 
x_83 = lean::cnstr_get(x_1, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_1, 1);
lean::inc(x_84);
lean::dec(x_1);
x_85 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_83);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_86 = lean::box(0);
x_87 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_83, x_86);
x_88 = lean::mk_nat_obj(0u);
x_89 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_84, x_2, x_84, x_88, x_87);
lean::dec(x_2);
lean::dec(x_84);
return x_89;
}
else
{
obj* x_90; obj* x_91; 
lean::dec(x_85);
lean::dec(x_83);
x_90 = lean::mk_nat_obj(0u);
x_91 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_freevars_24__collectArgs___spec__2(x_84, x_2, x_84, x_90, x_3);
lean::dec(x_2);
lean::dec(x_84);
return x_91;
}
}
case 13:
{
lean::dec(x_2);
return x_3;
}
default: 
{
obj* x_92; obj* x_93; obj* x_94; 
x_92 = lean::cnstr_get(x_1, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_1, 2);
lean::inc(x_93);
lean::dec(x_1);
x_94 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_2, x_92);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; 
x_95 = lean::box(0);
x_96 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_92, x_95);
x_1 = x_93;
x_3 = x_96;
goto _start;
}
else
{
lean::dec(x_94);
lean::dec(x_92);
x_1 = x_93;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_FreeIndices_collectFnBody(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_FreeIndices_collectFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_FnBody_collectFreeIndices(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_Lean_IR_FreeIndices_collectFnBody___main(x_1, x_3, x_2);
return x_4;
}
}
obj* l_Lean_IR_FnBody_freeIndices(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_2);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitVar(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_HasIndex_visitVar___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_HasIndex_visitJP(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_HasIndex_visitJP___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitJP(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_HasIndex_visitArg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean_nat_dec_eq(x_1, x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
obj* l_Lean_IR_HasIndex_visitArg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitArg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_HasIndex_visitArg(x_1, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean::dec(x_3);
return x_8;
}
}
}
}
uint8 l_Lean_IR_HasIndex_visitArgs(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_IR_HasIndex_visitArgs___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitArgs(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean_nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean::dec(x_3);
return x_9;
}
}
}
}
uint8 l_Lean_IR_HasIndex_visitParams(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitParams___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_IR_HasIndex_visitParams___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitParams(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_HasIndex_visitExpr(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_3, x_4);
return x_5;
}
case 1:
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_1, x_6);
return x_7;
}
case 2:
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 2);
x_10 = lean_nat_dec_eq(x_1, x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_9, x_11);
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
case 3:
{
obj* x_14; uint8 x_15; 
x_14 = lean::cnstr_get(x_2, 1);
x_15 = lean_nat_dec_eq(x_1, x_14);
return x_15;
}
case 4:
{
obj* x_16; uint8 x_17; 
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean_nat_dec_eq(x_1, x_16);
return x_17;
}
case 5:
{
obj* x_18; uint8 x_19; 
x_18 = lean::cnstr_get(x_2, 2);
x_19 = lean_nat_dec_eq(x_1, x_18);
return x_19;
}
case 6:
{
obj* x_20; obj* x_21; uint8 x_22; 
x_20 = lean::cnstr_get(x_2, 1);
x_21 = lean::mk_nat_obj(0u);
x_22 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_20, x_21);
return x_22;
}
case 7:
{
obj* x_23; obj* x_24; uint8 x_25; 
x_23 = lean::cnstr_get(x_2, 1);
x_24 = lean::mk_nat_obj(0u);
x_25 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_23, x_24);
return x_25;
}
case 8:
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::cnstr_get(x_2, 0);
x_27 = lean::cnstr_get(x_2, 1);
x_28 = lean_nat_dec_eq(x_1, x_26);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = lean::mk_nat_obj(0u);
x_30 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_27, x_29);
return x_30;
}
else
{
uint8 x_31; 
x_31 = 1;
return x_31;
}
}
case 11:
{
uint8 x_32; 
x_32 = 0;
return x_32;
}
default: 
{
obj* x_33; uint8 x_34; 
x_33 = lean::cnstr_get(x_2, 0);
x_34 = lean_nat_dec_eq(x_1, x_33);
return x_34;
}
}
}
}
obj* l_Lean_IR_HasIndex_visitExpr___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitExpr(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body(x_7);
lean::dec(x_7);
x_9 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean::dec(x_3);
return x_9;
}
}
}
}
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = lean::cnstr_get(x_2, 2);
x_5 = l_Lean_IR_HasIndex_visitExpr(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
case 1:
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_2, 2);
x_9 = lean::cnstr_get(x_2, 3);
x_10 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_8);
if (x_10 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
case 2:
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_13 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 2);
x_15 = lean::cnstr_get(x_2, 3);
x_16 = lean_nat_dec_eq(x_1, x_13);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_IR_HasIndex_visitArg(x_1, x_14);
if (x_17 == 0)
{
x_2 = x_15;
goto _start;
}
else
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = 1;
return x_20;
}
}
case 4:
{
obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_21 = lean::cnstr_get(x_2, 0);
x_22 = lean::cnstr_get(x_2, 2);
x_23 = lean::cnstr_get(x_2, 3);
x_24 = lean_nat_dec_eq(x_1, x_21);
if (x_24 == 0)
{
uint8 x_25; 
x_25 = lean_nat_dec_eq(x_1, x_22);
if (x_25 == 0)
{
x_2 = x_23;
goto _start;
}
else
{
uint8 x_27; 
x_27 = 1;
return x_27;
}
}
else
{
uint8 x_28; 
x_28 = 1;
return x_28;
}
}
case 5:
{
obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_29 = lean::cnstr_get(x_2, 0);
x_30 = lean::cnstr_get(x_2, 3);
x_31 = lean::cnstr_get(x_2, 4);
x_32 = lean_nat_dec_eq(x_1, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = lean_nat_dec_eq(x_1, x_30);
if (x_33 == 0)
{
x_2 = x_31;
goto _start;
}
else
{
uint8 x_35; 
x_35 = 1;
return x_35;
}
}
else
{
uint8 x_36; 
x_36 = 1;
return x_36;
}
}
case 8:
{
obj* x_37; obj* x_38; uint8 x_39; 
x_37 = lean::cnstr_get(x_2, 0);
x_38 = lean::cnstr_get(x_2, 1);
x_39 = lean_nat_dec_eq(x_1, x_37);
if (x_39 == 0)
{
x_2 = x_38;
goto _start;
}
else
{
uint8 x_41; 
x_41 = 1;
return x_41;
}
}
case 9:
{
obj* x_42; 
x_42 = lean::cnstr_get(x_2, 1);
x_2 = x_42;
goto _start;
}
case 10:
{
obj* x_44; obj* x_45; uint8 x_46; 
x_44 = lean::cnstr_get(x_2, 1);
x_45 = lean::cnstr_get(x_2, 2);
x_46 = lean_nat_dec_eq(x_1, x_44);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = lean::mk_nat_obj(0u);
x_48 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(x_1, x_45, x_47);
return x_48;
}
else
{
uint8 x_49; 
x_49 = 1;
return x_49;
}
}
case 11:
{
obj* x_50; uint8 x_51; 
x_50 = lean::cnstr_get(x_2, 0);
x_51 = l_Lean_IR_HasIndex_visitArg(x_1, x_50);
return x_51;
}
case 12:
{
obj* x_52; obj* x_53; uint8 x_54; 
x_52 = lean::cnstr_get(x_2, 0);
x_53 = lean::cnstr_get(x_2, 1);
x_54 = lean_nat_dec_eq(x_1, x_52);
if (x_54 == 0)
{
obj* x_55; uint8 x_56; 
x_55 = lean::mk_nat_obj(0u);
x_56 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_53, x_55);
return x_56;
}
else
{
uint8 x_57; 
x_57 = 1;
return x_57;
}
}
case 13:
{
uint8 x_58; 
x_58 = 0;
return x_58;
}
default: 
{
obj* x_59; obj* x_60; uint8 x_61; 
x_59 = lean::cnstr_get(x_2, 0);
x_60 = lean::cnstr_get(x_2, 2);
x_61 = lean_nat_dec_eq(x_1, x_59);
if (x_61 == 0)
{
x_2 = x_60;
goto _start;
}
else
{
uint8 x_63; 
x_63 = 1;
return x_63;
}
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_IR_HasIndex_visitFnBody___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_HasIndex_visitFnBody(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_HasIndex_visitFnBody___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_Arg_hasFreeVar(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_HasIndex_visitArg(x_2, x_1);
return x_3;
}
}
obj* l_Lean_IR_Arg_hasFreeVar___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Arg_hasFreeVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_Expr_hasFreeVar(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_HasIndex_visitExpr(x_2, x_1);
return x_3;
}
}
obj* l_Lean_IR_Expr_hasFreeVar___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Expr_hasFreeVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_FnBody_hasFreeVar(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_HasIndex_visitFnBody___main(x_2, x_1);
return x_3;
}
}
obj* l_Lean_IR_FnBody_hasFreeVar___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_FnBody_hasFreeVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_freevars(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_IR_MaxIndex_HasAndthen___closed__1 = _init_l_Lean_IR_MaxIndex_HasAndthen___closed__1();
lean::mark_persistent(l_Lean_IR_MaxIndex_HasAndthen___closed__1);
l_Lean_IR_MaxIndex_HasAndthen = _init_l_Lean_IR_MaxIndex_HasAndthen();
lean::mark_persistent(l_Lean_IR_MaxIndex_HasAndthen);
l_Lean_IR_MaxIndex_collectFnBody___main___closed__1 = _init_l_Lean_IR_MaxIndex_collectFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_MaxIndex_collectFnBody___main___closed__1);
l_Lean_IR_FreeIndices_HasAndthen___closed__1 = _init_l_Lean_IR_FreeIndices_HasAndthen___closed__1();
lean::mark_persistent(l_Lean_IR_FreeIndices_HasAndthen___closed__1);
l_Lean_IR_FreeIndices_HasAndthen = _init_l_Lean_IR_FreeIndices_HasAndthen();
lean::mark_persistent(l_Lean_IR_FreeIndices_HasAndthen);
l_Lean_IR_FreeIndices_collectFnBody___main___closed__1 = _init_l_Lean_IR_FreeIndices_collectFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_FreeIndices_collectFnBody___main___closed__1);
return w;
}
