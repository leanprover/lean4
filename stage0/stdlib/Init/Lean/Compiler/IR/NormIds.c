// Lean compiler output
// Module: Init.Lean.Compiler.IR.NormIds
// Imports: Init.Control.Reader Init.Control.Conditional Init.Lean.Compiler.IR.Basic
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
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_withVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UniqueIds_checkFnBody___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_monad;
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_mapVars(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_MtoN___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_replaceVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___main___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_withParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapExpr(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UniqueIds_checkId(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_uniqueIds(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_withJP___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_NormalizeIds_MtoN(lean_object*);
lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
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
lean_object* l_Lean_IR_UniqueIds_checkId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_1, x_4);
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
}
lean_object* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_3);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_UniqueIds_checkId(x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_4 = x_25;
x_5 = x_23;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(x_1, x_1, x_3, x_4, x_2);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 1;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkParams(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_3);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_4);
x_11 = l_Lean_IR_AltCore_body(x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_UniqueIds_checkFnBody___main(x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_4 = x_25;
x_5 = x_23;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_UniqueIds_checkFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_IR_UniqueIds_checkId(x_11, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_14);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_1 = x_12;
x_2 = x_20;
goto _start;
}
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_IR_UniqueIds_checkId(x_22, x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_23);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_IR_UniqueIds_checkParams(x_23, x_32);
lean_dec(x_23);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_24);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_34);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_1 = x_24;
x_2 = x_40;
goto _start;
}
}
}
case 10:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_array_get_size(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(x_42, x_42, x_43, x_44, x_2);
lean_dec(x_43);
lean_dec(x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = 1;
x_51 = lean_box(x_50);
lean_ctor_set(x_45, 0, x_51);
return x_45;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
lean_dec(x_57);
x_58 = 0;
x_59 = lean_box(x_58);
lean_ctor_set(x_45, 0, x_59);
return x_45;
}
else
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_dec(x_45);
x_61 = 0;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
}
default: 
{
lean_object* x_64; 
x_64 = lean_box(0);
x_3 = x_64;
goto block_10;
}
}
block_10:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_UniqueIds_checkParams(x_3, x_2);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_IR_UniqueIds_checkFnBody___main(x_4, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_IR_UniqueIds_checkParams(x_14, x_2);
lean_dec(x_14);
return x_15;
}
}
}
lean_object* l_Lean_IR_Decl_uniqueIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_IR_UniqueIds_checkDecl(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_NormalizeIds_normIndex(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_NormalizeIds_normIndex(x_6, x_2);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_NormalizeIds_normArg(x_9, x_1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_2, x_13);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = x_1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_4, x_3);
x_6 = x_5;
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_IR_NormalizeIds_normArgs(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Lean_IR_NormalizeIds_normArgs(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_2);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_IR_NormalizeIds_normIndex(x_14, x_2);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = l_Lean_IR_NormalizeIds_normIndex(x_18, x_2);
lean_dec(x_18);
x_21 = l_Lean_IR_NormalizeIds_normArgs(x_19, x_2);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = l_Lean_IR_NormalizeIds_normIndex(x_22, x_2);
lean_dec(x_22);
x_27 = l_Lean_IR_NormalizeIds_normArgs(x_25, x_2);
x_28 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_24);
return x_28;
}
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = l_Lean_IR_NormalizeIds_normIndex(x_30, x_2);
lean_dec(x_30);
lean_ctor_set(x_1, 1, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = l_Lean_IR_NormalizeIds_normIndex(x_33, x_2);
lean_dec(x_33);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 4:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 1);
x_38 = l_Lean_IR_NormalizeIds_normIndex(x_37, x_2);
lean_dec(x_37);
lean_ctor_set(x_1, 1, x_38);
return x_1;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_41 = l_Lean_IR_NormalizeIds_normIndex(x_40, x_2);
lean_dec(x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 5:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 2);
x_45 = l_Lean_IR_NormalizeIds_normIndex(x_44, x_2);
lean_dec(x_44);
lean_ctor_set(x_1, 2, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_49 = l_Lean_IR_NormalizeIds_normIndex(x_48, x_2);
lean_dec(x_48);
x_50 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
}
case 6:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 1);
x_53 = l_Lean_IR_NormalizeIds_normArgs(x_52, x_2);
lean_ctor_set(x_1, 1, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_1);
x_56 = l_Lean_IR_NormalizeIds_normArgs(x_55, x_2);
x_57 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
case 7:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 1);
x_60 = l_Lean_IR_NormalizeIds_normArgs(x_59, x_2);
lean_ctor_set(x_1, 1, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_1);
x_63 = l_Lean_IR_NormalizeIds_normArgs(x_62, x_2);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
case 8:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
x_68 = l_Lean_IR_NormalizeIds_normIndex(x_66, x_2);
lean_dec(x_66);
x_69 = l_Lean_IR_NormalizeIds_normArgs(x_67, x_2);
lean_ctor_set(x_1, 1, x_69);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_1);
x_72 = l_Lean_IR_NormalizeIds_normIndex(x_70, x_2);
lean_dec(x_70);
x_73 = l_Lean_IR_NormalizeIds_normArgs(x_71, x_2);
x_74 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
case 9:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_1);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_1, 1);
x_77 = l_Lean_IR_NormalizeIds_normIndex(x_76, x_2);
lean_dec(x_76);
lean_ctor_set(x_1, 1, x_77);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_1);
x_80 = l_Lean_IR_NormalizeIds_normIndex(x_79, x_2);
lean_dec(x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
case 10:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_1, 0);
x_84 = l_Lean_IR_NormalizeIds_normIndex(x_83, x_2);
lean_dec(x_83);
lean_ctor_set(x_1, 0, x_84);
return x_1;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
lean_dec(x_1);
x_86 = l_Lean_IR_NormalizeIds_normIndex(x_85, x_2);
lean_dec(x_85);
x_87 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
case 11:
{
return x_1;
}
case 12:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_1);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_1, 0);
x_90 = l_Lean_IR_NormalizeIds_normIndex(x_89, x_2);
lean_dec(x_89);
lean_ctor_set(x_1, 0, x_90);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_IR_NormalizeIds_normIndex(x_91, x_2);
lean_dec(x_91);
x_93 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
default: 
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_1);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_1, 0);
x_96 = l_Lean_IR_NormalizeIds_normIndex(x_95, x_2);
lean_dec(x_95);
lean_ctor_set(x_1, 0, x_96);
return x_1;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
lean_dec(x_1);
x_98 = l_Lean_IR_NormalizeIds_normIndex(x_97, x_2);
lean_dec(x_97);
x_99 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normExpr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_NormalizeIds_withVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_inc(x_4);
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_1, x_4);
x_8 = lean_apply_3(x_2, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withVar___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_NormalizeIds_withJP___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_inc(x_4);
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_1, x_4);
x_8 = lean_apply_3(x_2, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withJP___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_nat_add(x_5, x_10);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_13, x_5);
x_3 = x_11;
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_fget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_1);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_9;
x_16 = lean_array_fset(x_8, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_9);
x_21 = l_Lean_IR_NormalizeIds_normIndex(x_18, x_1);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = x_22;
x_26 = lean_array_fset(x_8, x_2, x_25);
lean_dec(x_2);
x_2 = x_24;
x_3 = x_26;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_NormalizeIds_withParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(x_1, x_1, x_5, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = x_1;
x_10 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(x_7, x_5, x_9);
x_11 = x_10;
x_12 = lean_apply_3(x_2, x_11, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_NormalizeIds_MtoN___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_IR_NormalizeIds_MtoN(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_MtoN___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_nat_add(x_5, x_10);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_13, x_5);
x_3 = x_11;
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_fget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_1);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_9;
x_16 = lean_array_fset(x_8, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_9);
x_21 = l_Lean_IR_NormalizeIds_normIndex(x_18, x_1);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = x_22;
x_26 = lean_array_fset(x_8, x_2, x_25);
lean_dec(x_2);
x_2 = x_24;
x_3 = x_26;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = x_8;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_3);
x_14 = l_Lean_IR_NormalizeIds_normFnBody___main(x_13, x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_11, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = x_11;
x_20 = lean_array_fset(x_10, x_1, x_19);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_20;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
lean_inc(x_3);
x_24 = l_Lean_IR_NormalizeIds_normFnBody___main(x_23, x_3, x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_1, x_28);
x_30 = x_27;
x_31 = lean_array_fset(x_10, x_1, x_30);
lean_dec(x_1);
x_1 = x_29;
x_2 = x_31;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_3);
x_35 = l_Lean_IR_NormalizeIds_normFnBody___main(x_34, x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_ctor_set(x_11, 0, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_1, x_38);
x_40 = x_11;
x_41 = lean_array_fset(x_10, x_1, x_40);
lean_dec(x_1);
x_1 = x_39;
x_2 = x_41;
x_4 = x_37;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
lean_dec(x_11);
lean_inc(x_3);
x_44 = l_Lean_IR_NormalizeIds_normFnBody___main(x_43, x_3, x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_1, x_48);
x_50 = x_47;
x_51 = lean_array_fset(x_10, x_1, x_50);
lean_dec(x_1);
x_1 = x_49;
x_2 = x_51;
x_4 = x_46;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_NormalizeIds_normFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_IR_NormalizeIds_normExpr(x_6, x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_3);
x_11 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_5, x_3);
x_12 = l_Lean_IR_NormalizeIds_normFnBody___main(x_7, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 3, x_14);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 0, x_3);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 0, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = l_Lean_IR_NormalizeIds_normExpr(x_20, x_2);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_inc(x_3);
x_25 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_18, x_3);
x_26 = l_Lean_IR_NormalizeIds_normFnBody___main(x_21, x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
case 1:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_38 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_34, x_34, x_37, x_2, x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = x_34;
x_42 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_39, x_37, x_41);
x_43 = x_42;
x_44 = l_Lean_IR_NormalizeIds_normFnBody___main(x_35, x_39, x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_46, x_47);
lean_inc(x_46);
x_49 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_33, x_46);
x_50 = l_Lean_IR_NormalizeIds_normFnBody___main(x_36, x_49, x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_ctor_set(x_1, 3, x_52);
lean_ctor_set(x_1, 2, x_45);
lean_ctor_set(x_1, 1, x_43);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set(x_50, 0, x_1);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_50);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_45);
lean_ctor_set(x_1, 1, x_43);
lean_ctor_set(x_1, 0, x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_1);
x_60 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_61 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_57, x_57, x_60, x_2, x_3);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = x_57;
x_65 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_62, x_60, x_64);
x_66 = x_65;
x_67 = l_Lean_IR_NormalizeIds_normFnBody___main(x_58, x_62, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_69, x_70);
lean_inc(x_69);
x_72 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_56, x_69);
x_73 = l_Lean_IR_NormalizeIds_normFnBody___main(x_59, x_72, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_68);
lean_ctor_set(x_77, 3, x_74);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
case 2:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_1, 2);
x_82 = lean_ctor_get(x_1, 3);
x_83 = l_Lean_IR_NormalizeIds_normIndex(x_80, x_2);
lean_dec(x_80);
x_84 = l_Lean_IR_NormalizeIds_normArg(x_81, x_2);
x_85 = l_Lean_IR_NormalizeIds_normFnBody___main(x_82, x_2, x_3);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_84);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set(x_85, 0, x_1);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_85, 0);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_85);
lean_ctor_set(x_1, 3, x_88);
lean_ctor_set(x_1, 2, x_84);
lean_ctor_set(x_1, 0, x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_ctor_get(x_1, 0);
x_92 = lean_ctor_get(x_1, 1);
x_93 = lean_ctor_get(x_1, 2);
x_94 = lean_ctor_get(x_1, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_1);
x_95 = l_Lean_IR_NormalizeIds_normIndex(x_91, x_2);
lean_dec(x_91);
x_96 = l_Lean_IR_NormalizeIds_normArg(x_93, x_2);
x_97 = l_Lean_IR_NormalizeIds_normFnBody___main(x_94, x_2, x_3);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_101, 2, x_96);
lean_ctor_set(x_101, 3, x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
case 3:
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_1);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_1, 0);
x_105 = lean_ctor_get(x_1, 2);
x_106 = l_Lean_IR_NormalizeIds_normIndex(x_104, x_2);
lean_dec(x_104);
x_107 = l_Lean_IR_NormalizeIds_normFnBody___main(x_105, x_2, x_3);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_107, 0);
lean_ctor_set(x_1, 2, x_109);
lean_ctor_set(x_1, 0, x_106);
lean_ctor_set(x_107, 0, x_1);
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_107);
lean_ctor_set(x_1, 2, x_110);
lean_ctor_set(x_1, 0, x_106);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_113 = lean_ctor_get(x_1, 0);
x_114 = lean_ctor_get(x_1, 1);
x_115 = lean_ctor_get(x_1, 2);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_1);
x_116 = l_Lean_IR_NormalizeIds_normIndex(x_113, x_2);
lean_dec(x_113);
x_117 = l_Lean_IR_NormalizeIds_normFnBody___main(x_115, x_2, x_3);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_114);
lean_ctor_set(x_121, 2, x_118);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
}
case 4:
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_1);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = lean_ctor_get(x_1, 2);
x_126 = lean_ctor_get(x_1, 3);
x_127 = l_Lean_IR_NormalizeIds_normIndex(x_124, x_2);
lean_dec(x_124);
x_128 = l_Lean_IR_NormalizeIds_normIndex(x_125, x_2);
lean_dec(x_125);
x_129 = l_Lean_IR_NormalizeIds_normFnBody___main(x_126, x_2, x_3);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_ctor_set(x_1, 3, x_131);
lean_ctor_set(x_1, 2, x_128);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set(x_129, 0, x_1);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
lean_ctor_set(x_1, 3, x_132);
lean_ctor_set(x_1, 2, x_128);
lean_ctor_set(x_1, 0, x_127);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = lean_ctor_get(x_1, 0);
x_136 = lean_ctor_get(x_1, 1);
x_137 = lean_ctor_get(x_1, 2);
x_138 = lean_ctor_get(x_1, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_1);
x_139 = l_Lean_IR_NormalizeIds_normIndex(x_135, x_2);
lean_dec(x_135);
x_140 = l_Lean_IR_NormalizeIds_normIndex(x_137, x_2);
lean_dec(x_137);
x_141 = l_Lean_IR_NormalizeIds_normFnBody___main(x_138, x_2, x_3);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_136);
lean_ctor_set(x_145, 2, x_140);
lean_ctor_set(x_145, 3, x_142);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
return x_146;
}
}
case 5:
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_1);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_148 = lean_ctor_get(x_1, 0);
x_149 = lean_ctor_get(x_1, 3);
x_150 = lean_ctor_get(x_1, 5);
x_151 = l_Lean_IR_NormalizeIds_normIndex(x_148, x_2);
lean_dec(x_148);
x_152 = l_Lean_IR_NormalizeIds_normIndex(x_149, x_2);
lean_dec(x_149);
x_153 = l_Lean_IR_NormalizeIds_normFnBody___main(x_150, x_2, x_3);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_ctor_set(x_1, 5, x_155);
lean_ctor_set(x_1, 3, x_152);
lean_ctor_set(x_1, 0, x_151);
lean_ctor_set(x_153, 0, x_1);
return x_153;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_153, 0);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_153);
lean_ctor_set(x_1, 5, x_156);
lean_ctor_set(x_1, 3, x_152);
lean_ctor_set(x_1, 0, x_151);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_159 = lean_ctor_get(x_1, 0);
x_160 = lean_ctor_get(x_1, 1);
x_161 = lean_ctor_get(x_1, 2);
x_162 = lean_ctor_get(x_1, 3);
x_163 = lean_ctor_get(x_1, 4);
x_164 = lean_ctor_get(x_1, 5);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_1);
x_165 = l_Lean_IR_NormalizeIds_normIndex(x_159, x_2);
lean_dec(x_159);
x_166 = l_Lean_IR_NormalizeIds_normIndex(x_162, x_2);
lean_dec(x_162);
x_167 = l_Lean_IR_NormalizeIds_normFnBody___main(x_164, x_2, x_3);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
x_171 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_160);
lean_ctor_set(x_171, 2, x_161);
lean_ctor_set(x_171, 3, x_166);
lean_ctor_set(x_171, 4, x_163);
lean_ctor_set(x_171, 5, x_168);
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_170;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_169);
return x_172;
}
}
case 6:
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_1);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_174 = lean_ctor_get(x_1, 0);
x_175 = lean_ctor_get(x_1, 2);
x_176 = l_Lean_IR_NormalizeIds_normIndex(x_174, x_2);
lean_dec(x_174);
x_177 = l_Lean_IR_NormalizeIds_normFnBody___main(x_175, x_2, x_3);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_177, 0);
lean_ctor_set(x_1, 2, x_179);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set(x_177, 0, x_1);
return x_177;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_177, 0);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_177);
lean_ctor_set(x_1, 2, x_180);
lean_ctor_set(x_1, 0, x_176);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_183 = lean_ctor_get(x_1, 0);
x_184 = lean_ctor_get(x_1, 1);
x_185 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_186 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_187 = lean_ctor_get(x_1, 2);
lean_inc(x_187);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_1);
x_188 = l_Lean_IR_NormalizeIds_normIndex(x_183, x_2);
lean_dec(x_183);
x_189 = l_Lean_IR_NormalizeIds_normFnBody___main(x_187, x_2, x_3);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set_uint8(x_193, sizeof(void*)*3, x_185);
lean_ctor_set_uint8(x_193, sizeof(void*)*3 + 1, x_186);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
}
case 7:
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_1);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_1, 0);
x_197 = lean_ctor_get(x_1, 2);
x_198 = l_Lean_IR_NormalizeIds_normIndex(x_196, x_2);
lean_dec(x_196);
x_199 = l_Lean_IR_NormalizeIds_normFnBody___main(x_197, x_2, x_3);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_199, 0);
lean_ctor_set(x_1, 2, x_201);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set(x_199, 0, x_1);
return x_199;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_199, 0);
x_203 = lean_ctor_get(x_199, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_199);
lean_ctor_set(x_1, 2, x_202);
lean_ctor_set(x_1, 0, x_198);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_1);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_205 = lean_ctor_get(x_1, 0);
x_206 = lean_ctor_get(x_1, 1);
x_207 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_208 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_209 = lean_ctor_get(x_1, 2);
lean_inc(x_209);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_1);
x_210 = l_Lean_IR_NormalizeIds_normIndex(x_205, x_2);
lean_dec(x_205);
x_211 = l_Lean_IR_NormalizeIds_normFnBody___main(x_209, x_2, x_3);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_206);
lean_ctor_set(x_215, 2, x_212);
lean_ctor_set_uint8(x_215, sizeof(void*)*3, x_207);
lean_ctor_set_uint8(x_215, sizeof(void*)*3 + 1, x_208);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
}
case 8:
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_1);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_218 = lean_ctor_get(x_1, 0);
x_219 = lean_ctor_get(x_1, 1);
x_220 = l_Lean_IR_NormalizeIds_normIndex(x_218, x_2);
lean_dec(x_218);
x_221 = l_Lean_IR_NormalizeIds_normFnBody___main(x_219, x_2, x_3);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 0);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_220);
lean_ctor_set(x_221, 0, x_1);
return x_221;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_221, 0);
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_221);
lean_ctor_set(x_1, 1, x_224);
lean_ctor_set(x_1, 0, x_220);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_1);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_227 = lean_ctor_get(x_1, 0);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_1);
x_229 = l_Lean_IR_NormalizeIds_normIndex(x_227, x_2);
lean_dec(x_227);
x_230 = l_Lean_IR_NormalizeIds_normFnBody___main(x_228, x_2, x_3);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_234, 0, x_229);
lean_ctor_set(x_234, 1, x_231);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
}
case 9:
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_1);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_237 = lean_ctor_get(x_1, 1);
x_238 = l_Lean_IR_NormalizeIds_normFnBody___main(x_237, x_2, x_3);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_238, 0);
lean_ctor_set(x_1, 1, x_240);
lean_ctor_set(x_238, 0, x_1);
return x_238;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_238, 0);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_238);
lean_ctor_set(x_1, 1, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_244 = lean_ctor_get(x_1, 0);
x_245 = lean_ctor_get(x_1, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_1);
x_246 = l_Lean_IR_NormalizeIds_normFnBody___main(x_245, x_2, x_3);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_244);
lean_ctor_set(x_250, 1, x_247);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
case 10:
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_1);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_253 = lean_ctor_get(x_1, 1);
x_254 = lean_ctor_get(x_1, 3);
x_255 = l_Lean_IR_NormalizeIds_normIndex(x_253, x_2);
lean_dec(x_253);
x_256 = x_254;
x_257 = lean_unsigned_to_nat(0u);
x_258 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3), 4, 2);
lean_closure_set(x_258, 0, x_257);
lean_closure_set(x_258, 1, x_256);
x_259 = x_258;
x_260 = lean_apply_2(x_259, x_2, x_3);
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_260, 0);
lean_ctor_set(x_1, 3, x_262);
lean_ctor_set(x_1, 1, x_255);
lean_ctor_set(x_260, 0, x_1);
return x_260;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_260, 0);
x_264 = lean_ctor_get(x_260, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_260);
lean_ctor_set(x_1, 3, x_263);
lean_ctor_set(x_1, 1, x_255);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_1);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_266 = lean_ctor_get(x_1, 0);
x_267 = lean_ctor_get(x_1, 1);
x_268 = lean_ctor_get(x_1, 2);
x_269 = lean_ctor_get(x_1, 3);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_1);
x_270 = l_Lean_IR_NormalizeIds_normIndex(x_267, x_2);
lean_dec(x_267);
x_271 = x_269;
x_272 = lean_unsigned_to_nat(0u);
x_273 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3), 4, 2);
lean_closure_set(x_273, 0, x_272);
lean_closure_set(x_273, 1, x_271);
x_274 = x_273;
x_275 = lean_apply_2(x_274, x_2, x_3);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
x_279 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_279, 0, x_266);
lean_ctor_set(x_279, 1, x_270);
lean_ctor_set(x_279, 2, x_268);
lean_ctor_set(x_279, 3, x_276);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_277);
return x_280;
}
}
case 11:
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_1);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_1, 0);
x_283 = l_Lean_IR_NormalizeIds_normArg(x_282, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_283);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_1);
lean_ctor_set(x_284, 1, x_3);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_1, 0);
lean_inc(x_285);
lean_dec(x_1);
x_286 = l_Lean_IR_NormalizeIds_normArg(x_285, x_2);
lean_dec(x_2);
x_287 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_287, 0, x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_3);
return x_288;
}
}
case 12:
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_1);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_1, 0);
x_291 = lean_ctor_get(x_1, 1);
x_292 = l_Lean_IR_NormalizeIds_normIndex(x_290, x_2);
lean_dec(x_290);
x_293 = l_Lean_IR_NormalizeIds_normArgs(x_291, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_293);
lean_ctor_set(x_1, 0, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_1);
lean_ctor_set(x_294, 1, x_3);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_295 = lean_ctor_get(x_1, 0);
x_296 = lean_ctor_get(x_1, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_1);
x_297 = l_Lean_IR_NormalizeIds_normIndex(x_295, x_2);
lean_dec(x_295);
x_298 = l_Lean_IR_NormalizeIds_normArgs(x_296, x_2);
lean_dec(x_2);
x_299 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_3);
return x_300;
}
}
default: 
{
lean_object* x_301; 
lean_dec(x_2);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_1);
lean_ctor_set(x_301, 1, x_3);
return x_301;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_NormalizeIds_normFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_nat_add(x_5, x_10);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_13, x_5);
x_3 = x_11;
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_fget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_1);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_9;
x_16 = lean_array_fset(x_8, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_9);
x_21 = l_Lean_IR_NormalizeIds_normIndex(x_18, x_1);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = x_22;
x_26 = lean_array_fset(x_8, x_2, x_25);
lean_dec(x_2);
x_2 = x_24;
x_3 = x_26;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1(x_5, x_5, x_7, x_2, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = x_5;
x_12 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2(x_9, x_7, x_11);
x_13 = x_12;
x_14 = l_Lean_IR_NormalizeIds_normFnBody___main(x_6, x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set(x_1, 1, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1(x_21, x_21, x_24, x_2, x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = x_21;
x_29 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2(x_26, x_24, x_28);
x_30 = x_29;
x_31 = l_Lean_IR_NormalizeIds_normFnBody___main(x_23, x_26, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_NormalizeIds_normDecl___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_IR_NormalizeIds_normDecl(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Lean_IR_MapVars_mapArgs___lambda__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = x_2;
x_5 = l_Id_monad;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___rarg(x_5, lean_box(0), x_3, x_6, x_4);
x_8 = x_7;
return x_8;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_MapVars_mapArgs(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l_Lean_IR_MapVars_mapArgs(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_2, 1, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_20 = lean_apply_1(x_1, x_18);
x_21 = l_Lean_IR_MapVars_mapArgs(x_1, x_19);
lean_ctor_set(x_2, 2, x_21);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_1);
x_26 = lean_apply_1(x_1, x_22);
x_27 = l_Lean_IR_MapVars_mapArgs(x_1, x_25);
x_28 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_24);
return x_28;
}
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_apply_1(x_1, x_30);
lean_ctor_set(x_2, 1, x_31);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_34 = lean_apply_1(x_1, x_33);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 4:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_apply_1(x_1, x_37);
lean_ctor_set(x_2, 1, x_38);
return x_2;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = lean_apply_1(x_1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 5:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_apply_1(x_1, x_44);
lean_ctor_set(x_2, 2, x_45);
return x_2;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_49 = lean_apply_1(x_1, x_48);
x_50 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
}
case 6:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = l_Lean_IR_MapVars_mapArgs(x_1, x_52);
lean_ctor_set(x_2, 1, x_53);
return x_2;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_2);
x_56 = l_Lean_IR_MapVars_mapArgs(x_1, x_55);
x_57 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
case 7:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_2, 1);
x_60 = l_Lean_IR_MapVars_mapArgs(x_1, x_59);
lean_ctor_set(x_2, 1, x_60);
return x_2;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = l_Lean_IR_MapVars_mapArgs(x_1, x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
case 8:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_68 = lean_apply_1(x_1, x_66);
x_69 = l_Lean_IR_MapVars_mapArgs(x_1, x_67);
lean_ctor_set(x_2, 1, x_69);
lean_ctor_set(x_2, 0, x_68);
return x_2;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_2, 0);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_2);
lean_inc(x_1);
x_72 = lean_apply_1(x_1, x_70);
x_73 = l_Lean_IR_MapVars_mapArgs(x_1, x_71);
x_74 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
case 9:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_2);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_2, 1);
x_77 = lean_apply_1(x_1, x_76);
lean_ctor_set(x_2, 1, x_77);
return x_2;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_2);
x_80 = lean_apply_1(x_1, x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
case 10:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_apply_1(x_1, x_83);
lean_ctor_set(x_2, 0, x_84);
return x_2;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_apply_1(x_1, x_85);
x_87 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
case 11:
{
lean_dec(x_1);
return x_2;
}
case 12:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_apply_1(x_1, x_89);
lean_ctor_set(x_2, 0, x_90);
return x_2;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
lean_dec(x_2);
x_92 = lean_apply_1(x_1, x_91);
x_93 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
default: 
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_apply_1(x_1, x_95);
lean_ctor_set(x_2, 0, x_96);
return x_2;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
lean_dec(x_2);
x_98 = lean_apply_1(x_1, x_97);
x_99 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapFnBody___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_5);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_12);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_6 = l_Lean_IR_MapVars_mapExpr(x_1, x_4);
x_7 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_5);
lean_ctor_set(x_2, 3, x_7);
lean_ctor_set(x_2, 2, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_IR_MapVars_mapExpr(x_1, x_10);
x_13 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_18 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_16);
x_19 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_17);
lean_ctor_set(x_2, 3, x_19);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_22);
x_25 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_23);
x_26 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
return x_26;
}
}
case 2:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_31 = lean_apply_1(x_1, x_28);
lean_inc(x_1);
x_32 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_30);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_apply_1(x_1, x_34);
lean_ctor_set(x_29, 0, x_35);
lean_ctor_set(x_2, 3, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_apply_1(x_1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_2, 3, x_32);
lean_ctor_set(x_2, 2, x_38);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
}
else
{
lean_dec(x_1);
lean_ctor_set(x_2, 3, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_2, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
lean_inc(x_1);
x_43 = lean_apply_1(x_1, x_39);
lean_inc(x_1);
x_44 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_46 = x_41;
} else {
 lean_dec_ref(x_41);
 x_46 = lean_box(0);
}
x_47 = lean_apply_1(x_1, x_45);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_44);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
x_50 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_44);
return x_50;
}
}
}
case 3:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_54 = lean_apply_1(x_1, x_52);
x_55 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_53);
lean_ctor_set(x_2, 2, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
lean_inc(x_1);
x_59 = lean_apply_1(x_1, x_56);
x_60 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_58);
x_61 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_60);
return x_61;
}
}
case 4:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_66 = lean_apply_1(x_1, x_63);
lean_inc(x_1);
x_67 = lean_apply_1(x_1, x_64);
x_68 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_65);
lean_ctor_set(x_2, 3, x_68);
lean_ctor_set(x_2, 2, x_67);
lean_ctor_set(x_2, 0, x_66);
return x_2;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_2);
lean_inc(x_1);
x_73 = lean_apply_1(x_1, x_69);
lean_inc(x_1);
x_74 = lean_apply_1(x_1, x_71);
x_75 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_72);
x_76 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_75);
return x_76;
}
}
case 5:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 3);
x_80 = lean_ctor_get(x_2, 5);
lean_inc(x_1);
x_81 = lean_apply_1(x_1, x_78);
lean_inc(x_1);
x_82 = lean_apply_1(x_1, x_79);
x_83 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_80);
lean_ctor_set(x_2, 5, x_83);
lean_ctor_set(x_2, 3, x_82);
lean_ctor_set(x_2, 0, x_81);
return x_2;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_2, 2);
x_87 = lean_ctor_get(x_2, 3);
x_88 = lean_ctor_get(x_2, 4);
x_89 = lean_ctor_get(x_2, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_2);
lean_inc(x_1);
x_90 = lean_apply_1(x_1, x_84);
lean_inc(x_1);
x_91 = lean_apply_1(x_1, x_87);
x_92 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_89);
x_93 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_86);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_88);
lean_ctor_set(x_93, 5, x_92);
return x_93;
}
}
case 6:
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_97 = lean_apply_1(x_1, x_95);
x_98 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_96);
lean_ctor_set(x_2, 2, x_98);
lean_ctor_set(x_2, 0, x_97);
return x_2;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_2, 1);
x_101 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_103 = lean_ctor_get(x_2, 2);
lean_inc(x_103);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_2);
lean_inc(x_1);
x_104 = lean_apply_1(x_1, x_99);
x_105 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_103);
x_106 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*3, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*3 + 1, x_102);
return x_106;
}
}
case 7:
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_2);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_2, 0);
x_109 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_110 = lean_apply_1(x_1, x_108);
x_111 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_109);
lean_ctor_set(x_2, 2, x_111);
lean_ctor_set(x_2, 0, x_110);
return x_2;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_ctor_get(x_2, 1);
x_114 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_115 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_116 = lean_ctor_get(x_2, 2);
lean_inc(x_116);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_2);
lean_inc(x_1);
x_117 = lean_apply_1(x_1, x_112);
x_118 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_116);
x_119 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*3 + 1, x_115);
return x_119;
}
}
case 8:
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_2);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_123 = lean_apply_1(x_1, x_121);
x_124 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_122);
lean_ctor_set(x_2, 1, x_124);
lean_ctor_set(x_2, 0, x_123);
return x_2;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_2, 0);
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_2);
lean_inc(x_1);
x_127 = lean_apply_1(x_1, x_125);
x_128 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_126);
x_129 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
case 9:
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_2);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_2, 1);
x_132 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_131);
lean_ctor_set(x_2, 1, x_132);
return x_2;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_2, 0);
x_134 = lean_ctor_get(x_2, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_2);
x_135 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_134);
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
case 10:
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_2);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_ctor_get(x_2, 1);
x_139 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_140 = lean_apply_1(x_1, x_138);
x_141 = lean_alloc_closure((void*)(l_Lean_IR_MapVars_mapFnBody___main___lambda__1___boxed), 3, 1);
lean_closure_set(x_141, 0, x_1);
x_142 = x_139;
x_143 = l_Id_monad;
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_Array_umapMAux___main___rarg(x_143, lean_box(0), x_141, x_144, x_142);
x_146 = x_145;
lean_ctor_set(x_2, 3, x_146);
lean_ctor_set(x_2, 1, x_140);
return x_2;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_147 = lean_ctor_get(x_2, 0);
x_148 = lean_ctor_get(x_2, 1);
x_149 = lean_ctor_get(x_2, 2);
x_150 = lean_ctor_get(x_2, 3);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_2);
lean_inc(x_1);
x_151 = lean_apply_1(x_1, x_148);
x_152 = lean_alloc_closure((void*)(l_Lean_IR_MapVars_mapFnBody___main___lambda__1___boxed), 3, 1);
lean_closure_set(x_152, 0, x_1);
x_153 = x_150;
x_154 = l_Id_monad;
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Array_umapMAux___main___rarg(x_154, lean_box(0), x_152, x_155, x_153);
x_157 = x_156;
x_158 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_151);
lean_ctor_set(x_158, 2, x_149);
lean_ctor_set(x_158, 3, x_157);
return x_158;
}
}
case 11:
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_2);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_apply_1(x_1, x_162);
lean_ctor_set(x_160, 0, x_163);
return x_2;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_apply_1(x_1, x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_2, 0, x_166);
return x_2;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
lean_dec(x_2);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_apply_1(x_1, x_168);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 1, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_1);
x_173 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_173, 0, x_167);
return x_173;
}
}
}
case 12:
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_2);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_2, 1);
x_176 = l_Lean_IR_MapVars_mapArgs(x_1, x_175);
lean_ctor_set(x_2, 1, x_176);
return x_2;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_2, 0);
x_178 = lean_ctor_get(x_2, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_2);
x_179 = l_Lean_IR_MapVars_mapArgs(x_1, x_178);
x_180 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapFnBody___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapFnBody___main___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_FnBody_mapVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_10, 0, x_2);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_3, x_19);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = x_24;
x_26 = lean_array_fset(x_9, x_3, x_25);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_3, x_32);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_1, x_2, x_5, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_10, 0, x_2);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_3, x_19);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = x_24;
x_26 = lean_array_fset(x_9, x_3, x_25);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_3, x_32);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_1, x_2, x_5, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_10, 0, x_2);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_3, x_19);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = x_24;
x_26 = lean_array_fset(x_9, x_3, x_25);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_3, x_32);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_1, x_2, x_5, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_10, 0, x_2);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_3, x_19);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = x_24;
x_26 = lean_array_fset(x_9, x_3, x_25);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_3, x_32);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_1, x_2, x_5, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_10, 0, x_2);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_3, x_19);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = x_24;
x_26 = lean_array_fset(x_9, x_3, x_25);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_3, x_32);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_1, x_2, x_5, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(x_1, x_2, x_5);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(x_1, x_2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
case 1:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_nat_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
}
}
case 2:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_nat_dec_eq(x_1, x_20);
lean_inc(x_2);
x_23 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(x_1, x_2, x_21);
if (x_22 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 2, x_23);
return x_3;
}
else
{
lean_dec(x_20);
lean_ctor_set(x_3, 2, x_23);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_28 = lean_nat_dec_eq(x_1, x_24);
lean_inc(x_2);
x_29 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(x_1, x_2, x_27);
if (x_28 == 0)
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_26);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_24);
x_31 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_26);
return x_31;
}
}
}
case 3:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_nat_dec_eq(x_1, x_33);
if (x_34 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_37 = lean_nat_dec_eq(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_36);
x_39 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_2);
return x_39;
}
}
}
case 4:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_nat_dec_eq(x_1, x_41);
if (x_42 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_41);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_45 = lean_nat_dec_eq(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_2);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_44);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_2);
return x_47;
}
}
}
case 5:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_3, 2);
x_50 = lean_nat_dec_eq(x_1, x_49);
if (x_50 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_49);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_3);
x_54 = lean_nat_dec_eq(x_1, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_2);
x_55 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_53);
x_56 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_2);
return x_56;
}
}
}
case 6:
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_3, 1);
x_59 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(x_1, x_2, x_58);
lean_ctor_set(x_3, 1, x_59);
return x_3;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get(x_3, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_3);
x_62 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(x_1, x_2, x_61);
x_63 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
case 7:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_3);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_3, 1);
x_66 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(x_1, x_2, x_65);
lean_ctor_set(x_3, 1, x_66);
return x_3;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_3);
x_69 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(x_1, x_2, x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
case 8:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_3, 0);
x_73 = lean_ctor_get(x_3, 1);
x_74 = lean_nat_dec_eq(x_1, x_72);
lean_inc(x_2);
x_75 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(x_1, x_2, x_73);
if (x_74 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 1, x_75);
return x_3;
}
else
{
lean_dec(x_72);
lean_ctor_set(x_3, 1, x_75);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_3);
x_78 = lean_nat_dec_eq(x_1, x_76);
lean_inc(x_2);
x_79 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(x_1, x_2, x_77);
if (x_78 == 0)
{
lean_object* x_80; 
lean_dec(x_2);
x_80 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_76);
x_81 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
case 9:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_3, 1);
x_84 = lean_nat_dec_eq(x_1, x_83);
if (x_84 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_83);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_3, 0);
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_3);
x_87 = lean_nat_dec_eq(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_2);
x_88 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec(x_86);
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_2);
return x_89;
}
}
}
case 10:
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_3);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_3, 0);
x_92 = lean_nat_dec_eq(x_1, x_91);
if (x_92 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_91);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
lean_dec(x_3);
x_94 = lean_nat_dec_eq(x_1, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_2);
x_95 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec(x_93);
x_96 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_96, 0, x_2);
return x_96;
}
}
}
case 11:
{
lean_dec(x_2);
return x_3;
}
case 12:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_3);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_3, 0);
x_99 = lean_nat_dec_eq(x_1, x_98);
if (x_99 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_98);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_3, 0);
lean_inc(x_100);
lean_dec(x_3);
x_101 = lean_nat_dec_eq(x_1, x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_2);
x_102 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_100);
x_103 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_103, 0, x_2);
return x_103;
}
}
}
default: 
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_3);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_3, 0);
x_106 = lean_nat_dec_eq(x_1, x_105);
if (x_106 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_105);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_3, 0);
lean_inc(x_107);
lean_dec(x_3);
x_108 = lean_nat_dec_eq(x_1, x_107);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_2);
x_109 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_107);
x_110 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_110, 0, x_2);
return x_110;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_2);
x_15 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_14);
lean_ctor_set(x_10, 1, x_15);
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_2);
x_21 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = x_22;
x_24 = lean_array_fset(x_9, x_3, x_23);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_2);
x_28 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = x_10;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
lean_inc(x_2);
x_33 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = x_34;
x_36 = lean_array_fset(x_9, x_3, x_35);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_36;
goto _start;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_3, x_16);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_10, 0, x_2);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_3, x_19);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = x_24;
x_26 = lean_array_fset(x_9, x_3, x_25);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_3, x_29);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_3, x_32);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = x_3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_1, x_2, x_5, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_2);
x_7 = l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2(x_1, x_2, x_5);
x_8 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_6);
lean_ctor_set(x_3, 3, x_8);
lean_ctor_set(x_3, 2, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_2);
x_13 = l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2(x_1, x_2, x_11);
x_14 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_2);
x_19 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_17);
x_20 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_18);
lean_ctor_set(x_3, 3, x_20);
lean_ctor_set(x_3, 2, x_19);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_2);
x_25 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_23);
x_26 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_24);
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
}
case 2:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_nat_dec_eq(x_1, x_29);
lean_inc(x_2);
x_33 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_31);
if (x_32 == 0)
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_nat_dec_eq(x_1, x_35);
if (x_36 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 3, x_33);
return x_3;
}
else
{
lean_dec(x_35);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_3, 3, x_33);
return x_3;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_nat_dec_eq(x_1, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 2, x_39);
return x_3;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 2, x_40);
return x_3;
}
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 3, x_33);
return x_3;
}
}
else
{
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_nat_dec_eq(x_1, x_42);
if (x_43 == 0)
{
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_42);
lean_inc(x_2);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_nat_dec_eq(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 2, x_46);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_47; 
lean_dec(x_44);
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 2, x_47);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
lean_ctor_set(x_3, 3, x_33);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_ctor_get(x_3, 2);
x_51 = lean_ctor_get(x_3, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_3);
x_52 = lean_nat_dec_eq(x_1, x_48);
lean_inc(x_2);
x_53 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_51);
if (x_52 == 0)
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_55 = x_50;
} else {
 lean_dec_ref(x_50);
 x_55 = lean_box(0);
}
x_56 = lean_nat_dec_eq(x_1, x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_54);
x_58 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_53);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_2);
x_60 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_53);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_2);
x_61 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_49);
lean_ctor_set(x_61, 2, x_50);
lean_ctor_set(x_61, 3, x_53);
return x_61;
}
}
else
{
lean_dec(x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
 x_63 = lean_box(0);
}
x_64 = lean_nat_dec_eq(x_1, x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
x_66 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_49);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_53);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_inc(x_2);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_2);
x_68 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_49);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_53);
return x_68;
}
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set(x_69, 3, x_53);
return x_69;
}
}
}
}
case 3:
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_3);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_3, 0);
x_72 = lean_ctor_get(x_3, 2);
x_73 = lean_nat_dec_eq(x_1, x_71);
lean_inc(x_2);
x_74 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_72);
if (x_73 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 2, x_74);
return x_3;
}
else
{
lean_dec(x_71);
lean_ctor_set(x_3, 2, x_74);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_3, 0);
x_76 = lean_ctor_get(x_3, 1);
x_77 = lean_ctor_get(x_3, 2);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_3);
x_78 = lean_nat_dec_eq(x_1, x_75);
lean_inc(x_2);
x_79 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_77);
if (x_78 == 0)
{
lean_object* x_80; 
lean_dec(x_2);
x_80 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_75);
x_81 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_81, 2, x_79);
return x_81;
}
}
}
case 4:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get(x_3, 2);
x_85 = lean_ctor_get(x_3, 3);
x_86 = lean_nat_dec_eq(x_1, x_83);
x_87 = lean_nat_dec_eq(x_1, x_84);
lean_inc(x_2);
x_88 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_85);
if (x_86 == 0)
{
if (x_87 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 3, x_88);
return x_3;
}
else
{
lean_dec(x_84);
lean_ctor_set(x_3, 3, x_88);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
else
{
lean_dec(x_83);
if (x_87 == 0)
{
lean_ctor_set(x_3, 3, x_88);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_84);
lean_inc(x_2);
lean_ctor_set(x_3, 3, x_88);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_3, 0);
x_90 = lean_ctor_get(x_3, 1);
x_91 = lean_ctor_get(x_3, 2);
x_92 = lean_ctor_get(x_3, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_3);
x_93 = lean_nat_dec_eq(x_1, x_89);
x_94 = lean_nat_dec_eq(x_1, x_91);
lean_inc(x_2);
x_95 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_92);
if (x_93 == 0)
{
if (x_94 == 0)
{
lean_object* x_96; 
lean_dec(x_2);
x_96 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_95);
return x_96;
}
else
{
lean_object* x_97; 
lean_dec(x_91);
x_97 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_2);
lean_ctor_set(x_97, 3, x_95);
return x_97;
}
}
else
{
lean_dec(x_89);
if (x_94 == 0)
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_91);
lean_ctor_set(x_98, 3, x_95);
return x_98;
}
else
{
lean_object* x_99; 
lean_dec(x_91);
lean_inc(x_2);
x_99 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_90);
lean_ctor_set(x_99, 2, x_2);
lean_ctor_set(x_99, 3, x_95);
return x_99;
}
}
}
}
case 5:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_3, 0);
x_102 = lean_ctor_get(x_3, 3);
x_103 = lean_ctor_get(x_3, 5);
x_104 = lean_nat_dec_eq(x_1, x_101);
x_105 = lean_nat_dec_eq(x_1, x_102);
lean_inc(x_2);
x_106 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_103);
if (x_104 == 0)
{
if (x_105 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 5, x_106);
return x_3;
}
else
{
lean_dec(x_102);
lean_ctor_set(x_3, 5, x_106);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
else
{
lean_dec(x_101);
if (x_105 == 0)
{
lean_ctor_set(x_3, 5, x_106);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_102);
lean_inc(x_2);
lean_ctor_set(x_3, 5, x_106);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_3, 0);
x_108 = lean_ctor_get(x_3, 1);
x_109 = lean_ctor_get(x_3, 2);
x_110 = lean_ctor_get(x_3, 3);
x_111 = lean_ctor_get(x_3, 4);
x_112 = lean_ctor_get(x_3, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_3);
x_113 = lean_nat_dec_eq(x_1, x_107);
x_114 = lean_nat_dec_eq(x_1, x_110);
lean_inc(x_2);
x_115 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_112);
if (x_113 == 0)
{
if (x_114 == 0)
{
lean_object* x_116; 
lean_dec(x_2);
x_116 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_108);
lean_ctor_set(x_116, 2, x_109);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set(x_116, 4, x_111);
lean_ctor_set(x_116, 5, x_115);
return x_116;
}
else
{
lean_object* x_117; 
lean_dec(x_110);
x_117 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_2);
lean_ctor_set(x_117, 4, x_111);
lean_ctor_set(x_117, 5, x_115);
return x_117;
}
}
else
{
lean_dec(x_107);
if (x_114 == 0)
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_118, 0, x_2);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_115);
return x_118;
}
else
{
lean_object* x_119; 
lean_dec(x_110);
lean_inc(x_2);
x_119 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_119, 0, x_2);
lean_ctor_set(x_119, 1, x_108);
lean_ctor_set(x_119, 2, x_109);
lean_ctor_set(x_119, 3, x_2);
lean_ctor_set(x_119, 4, x_111);
lean_ctor_set(x_119, 5, x_115);
return x_119;
}
}
}
}
case 6:
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_3);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_3, 0);
x_122 = lean_ctor_get(x_3, 2);
x_123 = lean_nat_dec_eq(x_1, x_121);
lean_inc(x_2);
x_124 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_122);
if (x_123 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 2, x_124);
return x_3;
}
else
{
lean_dec(x_121);
lean_ctor_set(x_3, 2, x_124);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_3, 0);
x_126 = lean_ctor_get(x_3, 1);
x_127 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_128 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_129 = lean_ctor_get(x_3, 2);
lean_inc(x_129);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_3);
x_130 = lean_nat_dec_eq(x_1, x_125);
lean_inc(x_2);
x_131 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_129);
if (x_130 == 0)
{
lean_object* x_132; 
lean_dec(x_2);
x_132 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_126);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*3, x_127);
lean_ctor_set_uint8(x_132, sizeof(void*)*3 + 1, x_128);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_125);
x_133 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_133, 0, x_2);
lean_ctor_set(x_133, 1, x_126);
lean_ctor_set(x_133, 2, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*3, x_127);
lean_ctor_set_uint8(x_133, sizeof(void*)*3 + 1, x_128);
return x_133;
}
}
}
case 7:
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_3);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_3, 0);
x_136 = lean_ctor_get(x_3, 2);
x_137 = lean_nat_dec_eq(x_1, x_135);
lean_inc(x_2);
x_138 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_136);
if (x_137 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 2, x_138);
return x_3;
}
else
{
lean_dec(x_135);
lean_ctor_set(x_3, 2, x_138);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_3, 0);
x_140 = lean_ctor_get(x_3, 1);
x_141 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_142 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_143 = lean_ctor_get(x_3, 2);
lean_inc(x_143);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_3);
x_144 = lean_nat_dec_eq(x_1, x_139);
lean_inc(x_2);
x_145 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_143);
if (x_144 == 0)
{
lean_object* x_146; 
lean_dec(x_2);
x_146 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_145);
lean_ctor_set_uint8(x_146, sizeof(void*)*3, x_141);
lean_ctor_set_uint8(x_146, sizeof(void*)*3 + 1, x_142);
return x_146;
}
else
{
lean_object* x_147; 
lean_dec(x_139);
x_147 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_147, 0, x_2);
lean_ctor_set(x_147, 1, x_140);
lean_ctor_set(x_147, 2, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*3, x_141);
lean_ctor_set_uint8(x_147, sizeof(void*)*3 + 1, x_142);
return x_147;
}
}
}
case 8:
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_3);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_3, 0);
x_150 = lean_ctor_get(x_3, 1);
x_151 = lean_nat_dec_eq(x_1, x_149);
lean_inc(x_2);
x_152 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_150);
if (x_151 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 1, x_152);
return x_3;
}
else
{
lean_dec(x_149);
lean_ctor_set(x_3, 1, x_152);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_3, 0);
x_154 = lean_ctor_get(x_3, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_3);
x_155 = lean_nat_dec_eq(x_1, x_153);
lean_inc(x_2);
x_156 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_154);
if (x_155 == 0)
{
lean_object* x_157; 
lean_dec(x_2);
x_157 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_153);
x_158 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_158, 0, x_2);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
case 9:
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_3);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_3, 1);
x_161 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_160);
lean_ctor_set(x_3, 1, x_161);
return x_3;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_3, 0);
x_163 = lean_ctor_get(x_3, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_3);
x_164 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_163);
x_165 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
case 10:
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_3);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_3, 1);
x_168 = lean_ctor_get(x_3, 3);
x_169 = lean_nat_dec_eq(x_1, x_167);
x_170 = x_168;
x_171 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_172 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_1, x_2, x_171, x_170);
x_173 = x_172;
if (x_169 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 3, x_173);
return x_3;
}
else
{
lean_dec(x_167);
lean_ctor_set(x_3, 3, x_173);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_3, 0);
x_175 = lean_ctor_get(x_3, 1);
x_176 = lean_ctor_get(x_3, 2);
x_177 = lean_ctor_get(x_3, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_3);
x_178 = lean_nat_dec_eq(x_1, x_175);
x_179 = x_177;
x_180 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_181 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_1, x_2, x_180, x_179);
x_182 = x_181;
if (x_178 == 0)
{
lean_object* x_183; 
lean_dec(x_2);
x_183 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_175);
lean_ctor_set(x_183, 2, x_176);
lean_ctor_set(x_183, 3, x_182);
return x_183;
}
else
{
lean_object* x_184; 
lean_dec(x_175);
x_184 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_184, 0, x_174);
lean_ctor_set(x_184, 1, x_2);
lean_ctor_set(x_184, 2, x_176);
lean_ctor_set(x_184, 3, x_182);
return x_184;
}
}
}
case 11:
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_3);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_nat_dec_eq(x_1, x_188);
if (x_189 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_188);
lean_ctor_set(x_186, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
lean_dec(x_186);
x_191 = lean_nat_dec_eq(x_1, x_190);
if (x_191 == 0)
{
lean_object* x_192; 
lean_dec(x_2);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_3, 0, x_192);
return x_3;
}
else
{
lean_object* x_193; 
lean_dec(x_190);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_2);
lean_ctor_set(x_3, 0, x_193);
return x_3;
}
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_3, 0);
lean_inc(x_194);
lean_dec(x_3);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = lean_nat_dec_eq(x_1, x_195);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_2);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_195);
x_199 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_195);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 1, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_2);
x_201 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
else
{
lean_object* x_202; 
lean_dec(x_2);
x_202 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_202, 0, x_194);
return x_202;
}
}
}
case 12:
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_3);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_3, 1);
x_205 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(x_1, x_2, x_204);
lean_ctor_set(x_3, 1, x_205);
return x_3;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_3, 0);
x_207 = lean_ctor_get(x_3, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_3);
x_208 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(x_1, x_2, x_207);
x_209 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
default: 
{
lean_dec(x_2);
return x_3;
}
}
}
}
lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapExpr___at_Lean_IR_FnBody_replaceVar___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_FnBody_replaceVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FnBody_replaceVar(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_Conditional(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Conditional(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
