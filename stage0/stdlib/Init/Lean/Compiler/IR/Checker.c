// Lean compiler output
// Module: Init.Lean.Compiler.IR.Checker
// Imports: Init.Lean.Compiler.IR.CompilerM
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
extern lean_object* l_Lean_Name_toString___closed__1;
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP___closed__1;
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markIndex___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_RBNode_findCore___main___at_Lean_IR_Checker_markIndex___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes___closed__1;
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_getDecl___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes___closed__2;
uint8_t l_Lean_IR_IRType_beq___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__3;
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___closed__1;
lean_object* l_RBNode_findCore___main___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___closed__2;
lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markIndex___closed__2;
lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
lean_object* l_Lean_IR_Checker_markIndex___closed__1;
lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__5;
lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* l_RBNode_findCore___main___at_Lean_IR_Checker_markIndex___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_lt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
lean_object* _init_l_Lean_IR_Checker_markIndex___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_Checker_markIndex___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable / joinpoint index ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_markIndex___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" has already been used");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_findCore___main___at_Lean_IR_Checker_markIndex___spec__1(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_6);
x_8 = l_Lean_IR_Checker_markIndex___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Nat_repr(x_1);
x_11 = l_Lean_IR_Checker_markIndex___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_Checker_markIndex___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = l_String_Iterator_extract___closed__1;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_18);
x_20 = l_Lean_IR_Checker_markIndex___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l_Nat_repr(x_1);
x_23 = l_Lean_IR_Checker_markIndex___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_IR_Checker_markIndex___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
}
lean_object* l_RBNode_findCore___main___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_findCore___main___at_Lean_IR_Checker_markIndex___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_1);
x_9 = l_Lean_IR_getDecl___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_getDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_Checker_checkVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown variable '");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_isLocalVar(x_4, x_1);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = l_Lean_IR_LocalContext_isParam(x_4, x_1);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Nat_repr(x_1);
x_10 = l_Lean_IR_VarId_HasToString___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Checker_checkVar___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_IR_Checker_markIndex___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = l_String_Iterator_extract___closed__1;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = l_Nat_repr(x_1);
x_22 = l_Lean_IR_VarId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_IR_Checker_checkVar___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Char_HasRepr___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = l_Lean_IR_Checker_markIndex___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_Checker_checkJP___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown join point '");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_isJP(x_4, x_1);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_checkJP___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_IR_Checker_markIndex___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Checker_checkVar(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_Checker_markIndex___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_IR_Checker_markIndex___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_IR_Checker_checkArg(x_9, x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_21 = x_13;
} else {
 lean_dec_ref(x_13);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_2 = x_11;
x_4 = x_24;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkEqTypes___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = l_Lean_IR_IRType_beq___main(x_1, x_2);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_IR_Checker_markIndex___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
}
lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkEqTypes(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_apply_1(x_2, x_1);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_Checker_markIndex___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_IR_IRType_isObj(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_Checker_markIndex___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_IR_IRType_isScalar(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_Checker_markIndex___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_getType(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_Checker_checkVar___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_Checker_getType(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_apply_1(x_2, x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Bool_DecidableEq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_5, 0, x_25);
return x_5;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_apply_1(x_2, x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = 1;
x_31 = l_Bool_DecidableEq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_IR_Checker_markIndex___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = l_Lean_IR_IRType_isObj(x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Bool_DecidableEq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = l_Lean_IR_IRType_isObj(x_25);
lean_dec(x_25);
x_27 = 1;
x_28 = l_Bool_DecidableEq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_IR_Checker_markIndex___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = l_Lean_IR_IRType_isScalar(x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Bool_DecidableEq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = l_Lean_IR_IRType_isScalar(x_25);
lean_dec(x_25);
x_27 = 1;
x_28 = l_Bool_DecidableEq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_IR_Checker_markIndex___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incorrect number of arguments to '");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" provided, ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_array_get_size(x_2);
x_23 = l_Lean_IR_Decl_params(x_21);
lean_dec(x_21);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_eq(x_22, x_24);
x_26 = 1;
x_27 = l_Bool_DecidableEq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_1);
x_30 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Nat_repr(x_22);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Nat_repr(x_24);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_41 = lean_string_append(x_39, x_40);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_41);
return x_5;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_42, x_3, x_18);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_6, 0);
lean_inc(x_44);
lean_dec(x_6);
x_45 = lean_array_get_size(x_2);
x_46 = l_Lean_IR_Decl_params(x_44);
lean_dec(x_44);
x_47 = lean_array_get_size(x_46);
lean_dec(x_46);
x_48 = lean_nat_dec_eq(x_45, x_47);
x_49 = 1;
x_50 = l_Bool_DecidableEq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_1);
x_53 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Nat_repr(x_45);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_60 = lean_string_append(x_58, x_59);
x_61 = l_Nat_repr(x_47);
x_62 = lean_string_append(x_60, x_61);
lean_dec(x_61);
x_63 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_5, 0, x_65);
return x_5;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_47);
lean_dec(x_45);
lean_free_object(x_5);
lean_dec(x_1);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_66, x_3, x_18);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; 
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
lean_dec(x_5);
x_69 = lean_ctor_get(x_6, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_70 = x_6;
} else {
 lean_dec_ref(x_6);
 x_70 = lean_box(0);
}
x_71 = lean_array_get_size(x_2);
x_72 = l_Lean_IR_Decl_params(x_69);
lean_dec(x_69);
x_73 = lean_array_get_size(x_72);
lean_dec(x_72);
x_74 = lean_nat_dec_eq(x_71, x_73);
x_75 = 1;
x_76 = l_Bool_DecidableEq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_77 = l_Lean_Name_toString___closed__1;
x_78 = l_Lean_Name_toStringWithSep___main(x_77, x_1);
x_79 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Nat_repr(x_71);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Nat_repr(x_73);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_90 = lean_string_append(x_88, x_89);
if (lean_is_scalar(x_70)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_70;
 lean_ctor_set_tag(x_91, 0);
}
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_68);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_93, x_3, x_68);
return x_94;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments too partial application '");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', num. args: ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", arity: ");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_array_get_size(x_2);
x_23 = l_Lean_IR_Decl_params(x_21);
lean_dec(x_21);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_repr(x_22);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Nat_repr(x_24);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_37);
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_38, x_3, x_18);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_array_get_size(x_2);
x_42 = l_Lean_IR_Decl_params(x_40);
lean_dec(x_40);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
x_44 = lean_nat_dec_lt(x_41, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = l_Lean_Name_toString___closed__1;
x_46 = l_Lean_Name_toStringWithSep___main(x_45, x_1);
x_47 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Nat_repr(x_41);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
x_53 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Nat_repr(x_43);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_5, 0, x_57);
return x_5;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
lean_dec(x_41);
lean_free_object(x_5);
lean_dec(x_1);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_58, x_3, x_18);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
lean_dec(x_5);
x_61 = lean_ctor_get(x_6, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_62 = x_6;
} else {
 lean_dec_ref(x_6);
 x_62 = lean_box(0);
}
x_63 = lean_array_get_size(x_2);
x_64 = l_Lean_IR_Decl_params(x_61);
lean_dec(x_61);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = lean_nat_dec_lt(x_63, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = l_Lean_Name_toString___closed__1;
x_68 = l_Lean_Name_toStringWithSep___main(x_67, x_1);
x_69 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_73 = l_Nat_repr(x_63);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_75 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_76 = lean_string_append(x_74, x_75);
x_77 = l_Nat_repr(x_65);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
if (lean_is_scalar(x_62)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_62;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_60);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_1);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_81, x_3, x_60);
return x_82;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid proj index");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkExpr___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_IR_IRType_isStruct(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_IR_IRType_isUnion(x_1);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = l_Lean_IR_CtorInfo_isRef(x_5);
lean_dec(x_5);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_12, x_3, x_4);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_23 = x_15;
} else {
 lean_dec_ref(x_15);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_27, x_3, x_26);
lean_dec(x_6);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
x_29 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_30, x_3, x_4);
lean_dec(x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_45, x_3, x_44);
lean_dec(x_6);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
x_47 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_48, x_3, x_4);
lean_dec(x_6);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_51);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_dec(x_50);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_63, x_3, x_62);
lean_dec(x_6);
return x_64;
}
}
}
}
case 1:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l_Lean_IR_Checker_checkObjVar(x_65, x_3, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_66, 0, x_72);
return x_66;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_67);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_dec(x_66);
x_79 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_78);
return x_79;
}
}
case 2:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
lean_dec(x_2);
x_82 = l_Lean_IR_Checker_checkObjVar(x_80, x_3, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_82, 0, x_88);
return x_82;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_83);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
lean_dec(x_82);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_81, x_95, x_3, x_94);
lean_dec(x_81);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_97);
if (x_100 == 0)
{
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_96, 0, x_102);
return x_96;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_97);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_dec(x_96);
x_109 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_108);
return x_109;
}
}
}
case 3:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_2, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
lean_dec(x_2);
x_112 = l_Lean_IR_Checker_getType(x_111, x_3, x_4);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
lean_dec(x_110);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_113);
if (x_116 == 0)
{
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_112, 0, x_118);
return x_112;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_dec(x_112);
x_120 = lean_ctor_get(x_113, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
return x_123;
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_113, 0);
lean_inc(x_124);
lean_dec(x_113);
switch (lean_obj_tag(x_124)) {
case 7:
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_110);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
lean_dec(x_112);
x_126 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_125);
return x_126;
}
case 8:
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_110);
x_127 = lean_ctor_get(x_112, 1);
lean_inc(x_127);
lean_dec(x_112);
x_128 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_127);
return x_128;
}
case 9:
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_112);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_112, 0);
lean_dec(x_130);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_110, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_110);
x_134 = l_Lean_IR_Checker_checkExpr___closed__2;
lean_ctor_set(x_112, 0, x_134);
return x_112;
}
else
{
lean_object* x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; 
x_135 = lean_array_fget(x_131, x_110);
lean_dec(x_110);
lean_dec(x_131);
x_136 = l_Lean_IR_IRType_beq___main(x_135, x_1);
lean_dec(x_135);
x_137 = 1;
x_138 = l_Bool_DecidableEq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_112, 0, x_139);
return x_112;
}
else
{
lean_object* x_140; 
x_140 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_112, 0, x_140);
return x_112;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_112, 1);
lean_inc(x_141);
lean_dec(x_112);
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
lean_dec(x_124);
x_143 = lean_array_get_size(x_142);
x_144 = lean_nat_dec_lt(x_110, x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_142);
lean_dec(x_110);
x_145 = l_Lean_IR_Checker_checkExpr___closed__2;
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
return x_146;
}
else
{
lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; 
x_147 = lean_array_fget(x_142, x_110);
lean_dec(x_110);
lean_dec(x_142);
x_148 = l_Lean_IR_IRType_beq___main(x_147, x_1);
lean_dec(x_147);
x_149 = 1;
x_150 = l_Bool_DecidableEq(x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_141);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lean_IR_Checker_markIndex___closed__1;
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_141);
return x_154;
}
}
}
}
case 10:
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_112);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_112, 0);
lean_dec(x_156);
x_157 = lean_ctor_get(x_124, 1);
lean_inc(x_157);
lean_dec(x_124);
x_158 = lean_array_get_size(x_157);
x_159 = lean_nat_dec_lt(x_110, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_157);
lean_dec(x_110);
x_160 = l_Lean_IR_Checker_checkExpr___closed__2;
lean_ctor_set(x_112, 0, x_160);
return x_112;
}
else
{
lean_object* x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; 
x_161 = lean_array_fget(x_157, x_110);
lean_dec(x_110);
lean_dec(x_157);
x_162 = l_Lean_IR_IRType_beq___main(x_161, x_1);
lean_dec(x_161);
x_163 = 1;
x_164 = l_Bool_DecidableEq(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_112, 0, x_165);
return x_112;
}
else
{
lean_object* x_166; 
x_166 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_112, 0, x_166);
return x_112;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_112, 1);
lean_inc(x_167);
lean_dec(x_112);
x_168 = lean_ctor_get(x_124, 1);
lean_inc(x_168);
lean_dec(x_124);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_110, x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_168);
lean_dec(x_110);
x_171 = l_Lean_IR_Checker_checkExpr___closed__2;
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; 
x_173 = lean_array_fget(x_168, x_110);
lean_dec(x_110);
lean_dec(x_168);
x_174 = l_Lean_IR_IRType_beq___main(x_173, x_1);
lean_dec(x_173);
x_175 = 1;
x_176 = l_Bool_DecidableEq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_167);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Lean_IR_Checker_markIndex___closed__1;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_167);
return x_180;
}
}
}
}
default: 
{
uint8_t x_181; 
lean_dec(x_124);
lean_dec(x_110);
x_181 = !lean_is_exclusive(x_112);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_112, 0);
lean_dec(x_182);
x_183 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_112, 0, x_183);
return x_112;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_112, 1);
lean_inc(x_184);
lean_dec(x_112);
x_185 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
}
}
case 4:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_2, 1);
lean_inc(x_187);
lean_dec(x_2);
x_188 = l_Lean_IR_Checker_checkObjVar(x_187, x_3, x_4);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_188);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_188, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
lean_dec(x_189);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_188, 0, x_194);
return x_188;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
lean_dec(x_188);
x_196 = lean_ctor_get(x_189, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_197 = x_189;
} else {
 lean_dec_ref(x_189);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
return x_199;
}
}
else
{
uint8_t x_200; 
lean_dec(x_189);
x_200 = !lean_is_exclusive(x_188);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_188, 0);
lean_dec(x_201);
x_202 = lean_box(5);
x_203 = l_Lean_IR_IRType_beq___main(x_1, x_202);
x_204 = 1;
x_205 = l_Bool_DecidableEq(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_188, 0, x_206);
return x_188;
}
else
{
lean_object* x_207; 
x_207 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_188, 0, x_207);
return x_188;
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_188, 1);
lean_inc(x_208);
lean_dec(x_188);
x_209 = lean_box(5);
x_210 = l_Lean_IR_IRType_beq___main(x_1, x_209);
x_211 = 1;
x_212 = l_Bool_DecidableEq(x_210, x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_208);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = l_Lean_IR_Checker_markIndex___closed__1;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_208);
return x_216;
}
}
}
}
case 5:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_2, 2);
lean_inc(x_217);
lean_dec(x_2);
x_218 = l_Lean_IR_Checker_checkObjVar(x_217, x_3, x_4);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
x_222 = !lean_is_exclusive(x_219);
if (x_222 == 0)
{
return x_218;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
lean_dec(x_219);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_218, 0, x_224);
return x_218;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
lean_dec(x_218);
x_226 = lean_ctor_get(x_219, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_225);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_219);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
lean_dec(x_218);
x_231 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_230);
return x_231;
}
}
case 6:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_2, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_2, 1);
lean_inc(x_233);
lean_dec(x_2);
x_234 = l_Lean_IR_Checker_checkFullApp(x_232, x_233, x_3, x_4);
lean_dec(x_233);
return x_234;
}
case 7:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_2, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 1);
lean_inc(x_236);
lean_dec(x_2);
x_237 = l_Lean_IR_Checker_checkPartialApp(x_235, x_236, x_3, x_4);
lean_dec(x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
uint8_t x_239; 
x_239 = !lean_is_exclusive(x_237);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_237, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_238);
if (x_241 == 0)
{
return x_237;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_238, 0);
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_237, 0, x_243);
return x_237;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = lean_ctor_get(x_237, 1);
lean_inc(x_244);
lean_dec(x_237);
x_245 = lean_ctor_get(x_238, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_246 = x_238;
} else {
 lean_dec_ref(x_238);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_244);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_238);
x_249 = lean_ctor_get(x_237, 1);
lean_inc(x_249);
lean_dec(x_237);
x_250 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_249);
return x_250;
}
}
case 8:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_2, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_2, 1);
lean_inc(x_252);
lean_dec(x_2);
x_253 = l_Lean_IR_Checker_checkObjVar(x_251, x_3, x_4);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
lean_dec(x_252);
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_253, 0);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_254);
if (x_257 == 0)
{
return x_253;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_254, 0);
lean_inc(x_258);
lean_dec(x_254);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_253, 0, x_259);
return x_253;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_ctor_get(x_253, 1);
lean_inc(x_260);
lean_dec(x_253);
x_261 = lean_ctor_get(x_254, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_262 = x_254;
} else {
 lean_dec_ref(x_254);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 1, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_260);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_254);
x_265 = lean_ctor_get(x_253, 1);
lean_inc(x_265);
lean_dec(x_253);
x_266 = lean_unsigned_to_nat(0u);
x_267 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_252, x_266, x_3, x_265);
lean_dec(x_252);
return x_267;
}
}
case 9:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_2, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_2, 1);
lean_inc(x_269);
lean_dec(x_2);
x_270 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_dec(x_269);
lean_dec(x_268);
x_272 = !lean_is_exclusive(x_270);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_270, 0);
lean_dec(x_273);
x_274 = !lean_is_exclusive(x_271);
if (x_274 == 0)
{
return x_270;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
lean_dec(x_271);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_270, 0, x_276);
return x_270;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_270, 1);
lean_inc(x_277);
lean_dec(x_270);
x_278 = lean_ctor_get(x_271, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 x_279 = x_271;
} else {
 lean_dec_ref(x_271);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 1, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_278);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_277);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
x_282 = lean_ctor_get(x_270, 1);
lean_inc(x_282);
lean_dec(x_270);
lean_inc(x_269);
x_283 = l_Lean_IR_Checker_checkScalarVar(x_269, x_3, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
lean_dec(x_269);
lean_dec(x_268);
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_283, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_284);
if (x_287 == 0)
{
return x_283;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_284, 0);
lean_inc(x_288);
lean_dec(x_284);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_283, 0, x_289);
return x_283;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_283, 1);
lean_inc(x_290);
lean_dec(x_283);
x_291 = lean_ctor_get(x_284, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_292 = x_284;
} else {
 lean_dec_ref(x_284);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 1, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_291);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_290);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_284);
x_295 = lean_ctor_get(x_283, 1);
lean_inc(x_295);
lean_dec(x_283);
x_296 = l_Lean_IR_Checker_getType(x_269, x_3, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
uint8_t x_298; 
lean_dec(x_268);
x_298 = !lean_is_exclusive(x_296);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_296, 0);
lean_dec(x_299);
x_300 = !lean_is_exclusive(x_297);
if (x_300 == 0)
{
return x_296;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_297, 0);
lean_inc(x_301);
lean_dec(x_297);
x_302 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_296, 0, x_302);
return x_296;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = lean_ctor_get(x_296, 1);
lean_inc(x_303);
lean_dec(x_296);
x_304 = lean_ctor_get(x_297, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_305 = x_297;
} else {
 lean_dec_ref(x_297);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 1, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_304);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_303);
return x_307;
}
}
else
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_296);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; uint8_t x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_296, 0);
lean_dec(x_309);
x_310 = lean_ctor_get(x_297, 0);
lean_inc(x_310);
lean_dec(x_297);
x_311 = l_Lean_IR_IRType_beq___main(x_310, x_268);
lean_dec(x_268);
lean_dec(x_310);
x_312 = 1;
x_313 = l_Bool_DecidableEq(x_311, x_312);
if (x_313 == 0)
{
lean_object* x_314; 
x_314 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_296, 0, x_314);
return x_296;
}
else
{
lean_object* x_315; 
x_315 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_296, 0, x_315);
return x_296;
}
}
else
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; uint8_t x_320; 
x_316 = lean_ctor_get(x_296, 1);
lean_inc(x_316);
lean_dec(x_296);
x_317 = lean_ctor_get(x_297, 0);
lean_inc(x_317);
lean_dec(x_297);
x_318 = l_Lean_IR_IRType_beq___main(x_317, x_268);
lean_dec(x_268);
lean_dec(x_317);
x_319 = 1;
x_320 = l_Bool_DecidableEq(x_318, x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_316);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_Lean_IR_Checker_markIndex___closed__1;
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_316);
return x_324;
}
}
}
}
}
}
case 10:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_2, 0);
lean_inc(x_325);
lean_dec(x_2);
x_326 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
uint8_t x_328; 
lean_dec(x_325);
x_328 = !lean_is_exclusive(x_326);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = lean_ctor_get(x_326, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_327);
if (x_330 == 0)
{
return x_326;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_327, 0);
lean_inc(x_331);
lean_dec(x_327);
x_332 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_326, 0, x_332);
return x_326;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_333 = lean_ctor_get(x_326, 1);
lean_inc(x_333);
lean_dec(x_326);
x_334 = lean_ctor_get(x_327, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_335 = x_327;
} else {
 lean_dec_ref(x_327);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 1, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_334);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_333);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_327);
x_338 = lean_ctor_get(x_326, 1);
lean_inc(x_338);
lean_dec(x_326);
x_339 = l_Lean_IR_Checker_checkObjVar(x_325, x_3, x_338);
return x_339;
}
}
case 11:
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_2, 0);
lean_inc(x_340);
lean_dec(x_2);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_340);
x_341 = l_Lean_IR_Checker_markIndex___closed__1;
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_4);
return x_342;
}
else
{
lean_object* x_343; 
lean_dec(x_340);
x_343 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
return x_343;
}
}
default: 
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_2, 0);
lean_inc(x_344);
lean_dec(x_2);
x_345 = l_Lean_IR_Checker_checkObjVar(x_344, x_3, x_4);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
if (lean_obj_tag(x_346) == 0)
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_345);
if (x_347 == 0)
{
lean_object* x_348; uint8_t x_349; 
x_348 = lean_ctor_get(x_345, 0);
lean_dec(x_348);
x_349 = !lean_is_exclusive(x_346);
if (x_349 == 0)
{
return x_345;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_346, 0);
lean_inc(x_350);
lean_dec(x_346);
x_351 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_345, 0, x_351);
return x_345;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_345, 1);
lean_inc(x_352);
lean_dec(x_345);
x_353 = lean_ctor_get(x_346, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_354 = x_346;
} else {
 lean_dec_ref(x_346);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_353);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_352);
return x_356;
}
}
else
{
uint8_t x_357; 
lean_dec(x_346);
x_357 = !lean_is_exclusive(x_345);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; uint8_t x_361; uint8_t x_362; 
x_358 = lean_ctor_get(x_345, 0);
lean_dec(x_358);
x_359 = lean_box(1);
x_360 = l_Lean_IR_IRType_beq___main(x_1, x_359);
x_361 = 1;
x_362 = l_Bool_DecidableEq(x_360, x_361);
if (x_362 == 0)
{
lean_object* x_363; 
x_363 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_345, 0, x_363);
return x_345;
}
else
{
lean_object* x_364; 
x_364 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_345, 0, x_364);
return x_345;
}
}
else
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_345, 1);
lean_inc(x_365);
lean_dec(x_345);
x_366 = lean_box(1);
x_367 = l_Lean_IR_IRType_beq___main(x_1, x_366);
x_368 = 1;
x_369 = l_Bool_DecidableEq(x_367, x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_365);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = l_Lean_IR_Checker_markIndex___closed__1;
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_365);
return x_373;
}
}
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkExpr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = l_Lean_IR_Checker_markIndex(x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_3 = x_13;
x_4 = x_28;
x_6 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1(x_1, x_1, x_8, x_6, x_3, x_4);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_22 = x_14;
} else {
 lean_dec_ref(x_14);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
lean_ctor_set(x_3, 1, x_26);
x_27 = lean_apply_2(x_2, x_3, x_25);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_3);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_30 = x_9;
} else {
 lean_dec_ref(x_9);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_7);
x_38 = lean_apply_2(x_2, x_37, x_35);
return x_38;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_withParams(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = l_Lean_IR_Checker_markIndex(x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_3 = x_13;
x_4 = x_28;
x_6 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = l_Lean_IR_Checker_markIndex___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_IR_AltCore_body(x_9);
lean_dec(x_9);
lean_inc(x_3);
x_13 = l_Lean_IR_Checker_checkFnBody___main(x_12, x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_22 = x_14;
} else {
 lean_dec_ref(x_14);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_2 = x_11;
x_4 = x_25;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = l_Lean_IR_Checker_checkExpr(x_5, x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_17 = x_9;
} else {
 lean_dec_ref(x_9);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(0, 1, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
lean_inc(x_4);
x_21 = l_Lean_IR_Checker_markIndex(x_4, x_2, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_22);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = l_Lean_IR_LocalContext_addLocal(x_35, x_4, x_5, x_6);
lean_ctor_set(x_2, 1, x_36);
x_1 = x_7;
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_41 = l_Lean_IR_LocalContext_addLocal(x_39, x_4, x_5, x_6);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_40);
x_1 = x_7;
x_2 = x_42;
x_3 = x_33;
goto _start;
}
}
}
}
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
lean_inc(x_44);
x_48 = l_Lean_IR_Checker_markIndex(x_44, x_2, x_3);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_48, 0, x_54);
return x_48;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_49);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 2);
lean_inc(x_63);
x_64 = lean_unsigned_to_nat(0u);
lean_inc(x_62);
x_65 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_45, x_45, x_64, x_62, x_2, x_60);
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_2, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_2, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_free_object(x_2);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
return x_65;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_65, 0, x_75);
return x_65;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_dec(x_65);
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_dec(x_65);
x_82 = lean_ctor_get(x_70, 0);
lean_inc(x_82);
lean_dec(x_70);
lean_inc(x_63);
lean_inc(x_61);
lean_ctor_set(x_2, 1, x_82);
lean_inc(x_46);
x_83 = l_Lean_IR_Checker_checkFnBody___main(x_46, x_2, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_83, 0, x_89);
return x_83;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_84);
x_95 = lean_ctor_get(x_83, 1);
lean_inc(x_95);
lean_dec(x_83);
x_96 = l_Lean_IR_LocalContext_addJP(x_62, x_44, x_45, x_46);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_61);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_63);
x_1 = x_47;
x_2 = x_97;
x_3 = x_95;
goto _start;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_2);
x_99 = lean_ctor_get(x_65, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_100 = lean_ctor_get(x_65, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_101 = x_65;
} else {
 lean_dec_ref(x_65);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
if (lean_is_scalar(x_101)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_101;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_65, 1);
lean_inc(x_106);
lean_dec(x_65);
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
lean_dec(x_99);
lean_inc(x_63);
lean_inc(x_61);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_61);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_63);
lean_inc(x_46);
x_109 = l_Lean_IR_Checker_checkFnBody___main(x_46, x_108, x_106);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_110);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
lean_dec(x_109);
x_118 = l_Lean_IR_LocalContext_addJP(x_62, x_44, x_45, x_46);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_61);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_63);
x_1 = x_47;
x_2 = x_119;
x_3 = x_117;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_1, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_1, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 3);
lean_inc(x_123);
lean_dec(x_1);
x_124 = l_Lean_IR_Checker_checkVar(x_121, x_2, x_3);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_124, 0);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_125);
if (x_128 == 0)
{
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
lean_dec(x_125);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_124, 0, x_130);
return x_124;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_133 = x_125;
} else {
 lean_dec_ref(x_125);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
x_136 = lean_ctor_get(x_124, 1);
lean_inc(x_136);
lean_dec(x_124);
x_137 = l_Lean_IR_Checker_checkArg(x_122, x_2, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
lean_dec(x_123);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_137, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
return x_137;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_137, 0, x_143);
return x_137;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_dec(x_137);
x_145 = lean_ctor_get(x_138, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_144);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_dec(x_138);
x_149 = lean_ctor_get(x_137, 1);
lean_inc(x_149);
lean_dec(x_137);
x_1 = x_123;
x_3 = x_149;
goto _start;
}
}
}
case 4:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_1, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_1, 3);
lean_inc(x_153);
lean_dec(x_1);
x_154 = l_Lean_IR_Checker_checkVar(x_151, x_2, x_3);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_154);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_154, 0);
lean_dec(x_157);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
return x_154;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
lean_dec(x_155);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_154, 0, x_160);
return x_154;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
lean_dec(x_154);
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_163 = x_155;
} else {
 lean_dec_ref(x_155);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_161);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_155);
x_166 = lean_ctor_get(x_154, 1);
lean_inc(x_166);
lean_dec(x_154);
x_167 = l_Lean_IR_Checker_checkVar(x_152, x_2, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
lean_dec(x_153);
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_167, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_168);
if (x_171 == 0)
{
return x_167;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
lean_dec(x_168);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_167, 0, x_173);
return x_167;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_167, 1);
lean_inc(x_174);
lean_dec(x_167);
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_176 = x_168;
} else {
 lean_dec_ref(x_168);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_174);
return x_178;
}
}
else
{
lean_object* x_179; 
lean_dec(x_168);
x_179 = lean_ctor_get(x_167, 1);
lean_inc(x_179);
lean_dec(x_167);
x_1 = x_153;
x_3 = x_179;
goto _start;
}
}
}
case 5:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_1, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_1, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_1, 5);
lean_inc(x_183);
lean_dec(x_1);
x_184 = l_Lean_IR_Checker_checkVar(x_181, x_2, x_3);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_184, 0);
lean_dec(x_187);
x_188 = !lean_is_exclusive(x_185);
if (x_188 == 0)
{
return x_184;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_184, 0, x_190);
return x_184;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_184, 1);
lean_inc(x_191);
lean_dec(x_184);
x_192 = lean_ctor_get(x_185, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_193 = x_185;
} else {
 lean_dec_ref(x_185);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_191);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_185);
x_196 = lean_ctor_get(x_184, 1);
lean_inc(x_196);
lean_dec(x_184);
x_197 = l_Lean_IR_Checker_checkVar(x_182, x_2, x_196);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
lean_dec(x_183);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_197, 0);
lean_dec(x_200);
x_201 = !lean_is_exclusive(x_198);
if (x_201 == 0)
{
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
lean_dec(x_198);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_197, 0, x_203);
return x_197;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_206 = x_198;
} else {
 lean_dec_ref(x_198);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_204);
return x_208;
}
}
else
{
lean_object* x_209; 
lean_dec(x_198);
x_209 = lean_ctor_get(x_197, 1);
lean_inc(x_209);
lean_dec(x_197);
x_1 = x_183;
x_3 = x_209;
goto _start;
}
}
}
case 8:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_1, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_1, 1);
lean_inc(x_212);
lean_dec(x_1);
x_213 = l_Lean_IR_Checker_checkVar(x_211, x_2, x_3);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
uint8_t x_215; 
lean_dec(x_212);
lean_dec(x_2);
x_215 = !lean_is_exclusive(x_213);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_213, 0);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_214);
if (x_217 == 0)
{
return x_213;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
lean_dec(x_214);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_213, 0, x_219);
return x_213;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_213, 1);
lean_inc(x_220);
lean_dec(x_213);
x_221 = lean_ctor_get(x_214, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 1, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_221);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_220);
return x_224;
}
}
else
{
lean_object* x_225; 
lean_dec(x_214);
x_225 = lean_ctor_get(x_213, 1);
lean_inc(x_225);
lean_dec(x_213);
x_1 = x_212;
x_3 = x_225;
goto _start;
}
}
case 9:
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_1, 1);
lean_inc(x_227);
lean_dec(x_1);
x_1 = x_227;
goto _start;
}
case 10:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_1, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_1, 3);
lean_inc(x_230);
lean_dec(x_1);
x_231 = l_Lean_IR_Checker_checkVar(x_229, x_2, x_3);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
uint8_t x_233; 
lean_dec(x_230);
lean_dec(x_2);
x_233 = !lean_is_exclusive(x_231);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_231, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_232);
if (x_235 == 0)
{
return x_231;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_232, 0);
lean_inc(x_236);
lean_dec(x_232);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_231, 0, x_237);
return x_231;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_231, 1);
lean_inc(x_238);
lean_dec(x_231);
x_239 = lean_ctor_get(x_232, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_240 = x_232;
} else {
 lean_dec_ref(x_232);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_232);
x_243 = lean_ctor_get(x_231, 1);
lean_inc(x_243);
lean_dec(x_231);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_230, x_244, x_2, x_243);
lean_dec(x_230);
return x_245;
}
}
case 11:
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_1, 0);
lean_inc(x_246);
lean_dec(x_1);
x_247 = l_Lean_IR_Checker_checkArg(x_246, x_2, x_3);
lean_dec(x_2);
return x_247;
}
case 12:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_1, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_1, 1);
lean_inc(x_249);
lean_dec(x_1);
x_250 = l_Lean_IR_Checker_checkJP(x_248, x_2, x_3);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
lean_dec(x_249);
lean_dec(x_2);
x_252 = !lean_is_exclusive(x_250);
if (x_252 == 0)
{
lean_object* x_253; uint8_t x_254; 
x_253 = lean_ctor_get(x_250, 0);
lean_dec(x_253);
x_254 = !lean_is_exclusive(x_251);
if (x_254 == 0)
{
return x_250;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_250, 0, x_256);
return x_250;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
lean_dec(x_250);
x_258 = lean_ctor_get(x_251, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_259 = x_251;
} else {
 lean_dec_ref(x_251);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_257);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_251);
x_262 = lean_ctor_get(x_250, 1);
lean_inc(x_262);
lean_dec(x_250);
x_263 = lean_unsigned_to_nat(0u);
x_264 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_249, x_263, x_2, x_262);
lean_dec(x_2);
lean_dec(x_249);
return x_264;
}
}
case 13:
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_2);
x_265 = l_Lean_IR_Checker_markIndex___closed__1;
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_3);
return x_266;
}
default: 
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_1, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_1, 2);
lean_inc(x_268);
lean_dec(x_1);
x_269 = l_Lean_IR_Checker_checkVar(x_267, x_2, x_3);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
lean_dec(x_268);
lean_dec(x_2);
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_269, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_270);
if (x_273 == 0)
{
return x_269;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_270, 0);
lean_inc(x_274);
lean_dec(x_270);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_269, 0, x_275);
return x_269;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_269, 1);
lean_inc(x_276);
lean_dec(x_269);
x_277 = lean_ctor_get(x_270, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_278 = x_270;
} else {
 lean_dec_ref(x_270);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_276);
return x_280;
}
}
else
{
lean_object* x_281; 
lean_dec(x_270);
x_281 = lean_ctor_get(x_269, 1);
lean_inc(x_281);
lean_dec(x_269);
x_1 = x_268;
x_3 = x_281;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = l_Lean_IR_Checker_markIndex(x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_3 = x_13;
x_4 = x_28;
x_6 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = l_Lean_IR_Checker_markIndex(x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_3 = x_13;
x_4 = x_28;
x_6 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1(x_4, x_4, x_9, x_7, x_2, x_3);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_23 = x_15;
} else {
 lean_dec_ref(x_15);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_27);
x_28 = l_Lean_IR_Checker_checkFnBody___main(x_5, x_2, x_26);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_31 = x_10;
} else {
 lean_dec_ref(x_10);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_8);
x_39 = l_Lean_IR_Checker_checkFnBody___main(x_5, x_38, x_36);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2(x_40, x_40, x_42, x_41, x_2, x_3);
lean_dec(x_2);
lean_dec(x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_43, 0, x_49);
return x_43;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_44);
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_43, 0);
lean_dec(x_56);
x_57 = l_Lean_IR_Checker_markIndex___closed__1;
lean_ctor_set(x_43, 0, x_57);
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
x_59 = l_Lean_IR_Checker_markIndex___closed__1;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_IR_checkDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IR check failed at '");
return x_1;
}
}
lean_object* _init_l_Lean_IR_checkDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', error: ");
return x_1;
}
}
lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_getEnv___rarg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_inc(x_2);
x_10 = l_Lean_IR_Checker_checkDecl(x_2, x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = l_Lean_IR_checkDecl___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_checkDecl___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_12);
lean_dec(x_12);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_1);
lean_inc(x_2);
x_26 = l_Lean_IR_Checker_checkDecl(x_2, x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_29);
x_32 = l_Lean_IR_checkDecl___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_IR_checkDecl___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_28);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
return x_39;
}
}
}
}
lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = l_Lean_IR_checkDecl(x_1, x_10, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_IR_checkDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_4, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_checkDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Checker(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Checker_markIndex___closed__1 = _init_l_Lean_IR_Checker_markIndex___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__1);
l_Lean_IR_Checker_markIndex___closed__2 = _init_l_Lean_IR_Checker_markIndex___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__2);
l_Lean_IR_Checker_markIndex___closed__3 = _init_l_Lean_IR_Checker_markIndex___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__3);
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
l_Lean_IR_Checker_checkEqTypes___closed__1 = _init_l_Lean_IR_Checker_checkEqTypes___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__1);
l_Lean_IR_Checker_checkEqTypes___closed__2 = _init_l_Lean_IR_Checker_checkEqTypes___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__2);
l_Lean_IR_Checker_checkFullApp___closed__1 = _init_l_Lean_IR_Checker_checkFullApp___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__1);
l_Lean_IR_Checker_checkFullApp___closed__2 = _init_l_Lean_IR_Checker_checkFullApp___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__2);
l_Lean_IR_Checker_checkFullApp___closed__3 = _init_l_Lean_IR_Checker_checkFullApp___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__3);
l_Lean_IR_Checker_checkPartialApp___closed__1 = _init_l_Lean_IR_Checker_checkPartialApp___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__1);
l_Lean_IR_Checker_checkPartialApp___closed__2 = _init_l_Lean_IR_Checker_checkPartialApp___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__2);
l_Lean_IR_Checker_checkPartialApp___closed__3 = _init_l_Lean_IR_Checker_checkPartialApp___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__3);
l_Lean_IR_Checker_checkExpr___closed__1 = _init_l_Lean_IR_Checker_checkExpr___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__1);
l_Lean_IR_Checker_checkExpr___closed__2 = _init_l_Lean_IR_Checker_checkExpr___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__2);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__1);
l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
