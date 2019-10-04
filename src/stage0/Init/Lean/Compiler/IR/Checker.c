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
lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_getDecl___closed__1;
lean_object* l_Lean_IR_Checker_checkType(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq(uint8_t, uint8_t);
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__4;
lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFnBody___main___closed__1;
lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFnBody___main___closed__2;
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkType___closed__1;
lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___closed__2;
lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_IR_Checker_checkFnBody___main___closed__4;
lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFnBody___main___closed__3;
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__3;
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar___closed__2;
lean_object* l_Lean_IR_Checker_checkScalarType(uint8_t, lean_object*);
lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___closed__1;
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(uint8_t);
lean_object* l_Lean_IR_Checker_checkVar___closed__1;
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjType(uint8_t, lean_object*);
lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2;
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFnBody___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP___closed__1;
lean_object* l_Lean_IR_Checker_checkType___closed__2;
uint8_t l_Lean_IR_IRType_isObj(uint8_t);
lean_object* l_Lean_IR_Checker_checkExpr(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_IR_findEnvDecl_x27(x_3, x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = l_Lean_IR_getDecl___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_getDecl(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_isLocalVar(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_IR_LocalContext_isParam(x_3, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
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
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lean_IR_Checker_checkVar___closed__2;
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Lean_IR_Checker_checkVar___closed__2;
return x_15;
}
}
}
lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkVar(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_isJP(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_IR_Checker_checkJP___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = l_Lean_IR_Checker_checkVar___closed__2;
return x_13;
}
}
}
lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkJP(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkVar(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkVar___closed__2;
return x_5;
}
}
}
lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Lean_IR_Checker_checkVar___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_10 = l_Lean_IR_Checker_checkArg(x_7, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_dec(x_10);
x_2 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkArgs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkType___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkType(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(x_1);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkType___closed__2;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkVar___closed__2;
return x_8;
}
}
}
lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_IR_Checker_checkType(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkObjType(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isObj(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkType___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkVar___closed__2;
return x_5;
}
}
}
lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkObjType(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkScalarType(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isScalar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkType___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkVar___closed__2;
return x_5;
}
}
}
lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkScalarType(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_Lean_IR_LocalContext_getType(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
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
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_1(x_2, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_IR_Checker_checkType___closed__2;
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_IR_Checker_checkVar___closed__2;
return x_18;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_getType(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_IR_Checker_checkVar___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_IRType_isObj(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_IR_Checker_checkType___closed__2;
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
return x_17;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkObjVar(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_IR_LocalContext_getType(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_IR_Checker_checkVar___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_IRType_isScalar(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_IR_Checker_checkType___closed__2;
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
return x_17;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_IR_Checker_getDecl(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_1);
x_16 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_repr(x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_repr(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_28, x_3);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
lean_dec(x_4);
x_31 = lean_array_get_size(x_2);
x_32 = l_Lean_IR_Decl_params(x_30);
lean_dec(x_30);
x_33 = lean_array_get_size(x_32);
lean_dec(x_32);
x_34 = lean_nat_dec_eq(x_31, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = l_Lean_Name_toString___closed__1;
x_36 = l_Lean_Name_toStringWithSep___main(x_35, x_1);
x_37 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Nat_repr(x_31);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Nat_repr(x_33);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_50, x_3);
return x_51;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_IR_Checker_getDecl(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_1);
x_16 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_repr(x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_repr(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_26, x_3);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_array_get_size(x_2);
x_30 = l_Lean_IR_Decl_params(x_28);
lean_dec(x_28);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_nat_dec_lt(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_1);
x_35 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Nat_repr(x_29);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Nat_repr(x_31);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_46, x_3);
return x_47;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkExpr(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_IR_CtorInfo_isRef(x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_7, x_3);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_5, x_13, x_3);
lean_dec(x_5);
return x_14;
}
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_IR_Checker_checkObjVar(x_15, x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_16, x_21, x_3);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_26;
}
}
}
case 4:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_IR_Checker_checkObjVar(x_27, x_3);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; uint8_t x_33; 
lean_dec(x_28);
x_32 = 5;
x_33 = l_Lean_IR_IRType_beq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_IR_Checker_checkType___closed__2;
return x_34;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_IR_Checker_checkVar___closed__2;
return x_35;
}
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
lean_dec(x_2);
x_37 = l_Lean_IR_Checker_checkObjVar(x_36, x_3);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_37);
x_41 = l_Lean_IR_Checker_checkScalarType(x_1, x_3);
return x_41;
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_IR_Checker_checkFullApp(x_42, x_43, x_3);
lean_dec(x_43);
return x_44;
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_IR_Checker_checkPartialApp(x_45, x_46, x_3);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_47);
x_51 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_51;
}
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l_Lean_IR_Checker_checkObjVar(x_52, x_3);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_53);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_53, x_58, x_3);
lean_dec(x_53);
return x_59;
}
}
case 9:
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
lean_dec(x_2);
x_62 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_dec(x_61);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_62);
lean_inc(x_61);
x_66 = l_Lean_IR_Checker_checkScalarVar(x_61, x_3);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_61);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_3, 1);
x_73 = l_Lean_IR_LocalContext_getType(x_72, x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = l_Nat_repr(x_61);
x_75 = l_Lean_IR_VarId_HasToString___closed__1;
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = l_Lean_IR_Checker_checkVar___closed__1;
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
x_79 = l_Char_HasRepr___closed__1;
x_80 = lean_string_append(x_78, x_79);
lean_ctor_set_tag(x_66, 0);
lean_ctor_set(x_66, 0, x_80);
return x_66;
}
else
{
lean_object* x_81; uint8_t x_82; uint8_t x_83; 
lean_free_object(x_66);
lean_dec(x_61);
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
x_83 = l_Lean_IR_IRType_beq(x_82, x_60);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = l_Lean_IR_Checker_checkType___closed__2;
return x_84;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_IR_Checker_checkVar___closed__2;
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
x_86 = lean_ctor_get(x_3, 1);
x_87 = l_Lean_IR_LocalContext_getType(x_86, x_61);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = l_Nat_repr(x_61);
x_89 = l_Lean_IR_VarId_HasToString___closed__1;
x_90 = lean_string_append(x_89, x_88);
lean_dec(x_88);
x_91 = l_Lean_IR_Checker_checkVar___closed__1;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = l_Char_HasRepr___closed__1;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; uint8_t x_98; 
lean_dec(x_61);
x_96 = lean_ctor_get(x_87, 0);
lean_inc(x_96);
lean_dec(x_87);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
x_98 = l_Lean_IR_IRType_beq(x_97, x_60);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_IR_Checker_checkType___closed__2;
return x_99;
}
else
{
lean_object* x_100; 
x_100 = l_Lean_IR_Checker_checkVar___closed__2;
return x_100;
}
}
}
}
}
}
case 10:
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
lean_dec(x_2);
x_102 = l_Lean_IR_Checker_checkScalarType(x_1, x_3);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
lean_dec(x_101);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_102);
x_106 = l_Lean_IR_Checker_checkObjVar(x_101, x_3);
return x_106;
}
}
case 11:
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_2, 0);
lean_inc(x_107);
lean_dec(x_2);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_107);
x_108 = l_Lean_IR_Checker_checkVar___closed__2;
return x_108;
}
else
{
lean_object* x_109; 
lean_dec(x_107);
x_109 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_109;
}
}
case 12:
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_2, 0);
lean_inc(x_110);
lean_dec(x_2);
x_111 = l_Lean_IR_Checker_checkObjVar(x_110, x_3);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
uint8_t x_115; uint8_t x_116; 
lean_dec(x_111);
x_115 = 1;
x_116 = l_Lean_IR_IRType_beq(x_1, x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = l_Lean_IR_Checker_checkType___closed__2;
return x_117;
}
else
{
lean_object* x_118; 
x_118 = l_Lean_IR_Checker_checkVar___closed__2;
return x_118;
}
}
}
case 13:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
lean_dec(x_2);
x_120 = l_Lean_IR_Checker_checkObjVar(x_119, x_3);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
uint8_t x_124; uint8_t x_125; 
lean_dec(x_120);
x_124 = 1;
x_125 = l_Lean_IR_IRType_beq(x_1, x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = l_Lean_IR_Checker_checkType___closed__2;
return x_126;
}
else
{
lean_object* x_127; 
x_127 = l_Lean_IR_Checker_checkVar___closed__2;
return x_127;
}
}
}
default: 
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_2, 1);
lean_inc(x_128);
lean_dec(x_2);
x_129 = l_Lean_IR_Checker_checkObjVar(x_128, x_3);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
return x_129;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
else
{
lean_object* x_133; 
lean_dec(x_129);
x_133 = l_Lean_IR_Checker_checkObjType(x_1, x_3);
return x_133;
}
}
}
}
}
lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_IR_Checker_checkExpr(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parameter declaration, shadowing is not allowed");
return x_1;
}
}
lean_object* _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2;
return x_16;
}
}
}
}
lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_1, x_1, x_7, x_5, x_3);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_13; 
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_16);
x_17 = lean_apply_1(x_2, x_3);
return x_17;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_19 = x_8;
} else {
 lean_dec_ref(x_8);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_6);
x_23 = lean_apply_1(x_2, x_22);
return x_23;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_withParams(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2;
return x_16;
}
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lean_IR_Checker_checkVar___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_10 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
lean_inc(x_3);
x_11 = l_Lean_IR_Checker_checkFnBody___main(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_dec(x_11);
x_2 = x_9;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_IR_Checker_checkFnBody___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid variable declaration, shadowing is not allowed");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkFnBody___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkFnBody___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_Checker_checkFnBody___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid join point declaration, shadowing is not allowed");
return x_1;
}
}
lean_object* _init_l_Lean_IR_Checker_checkFnBody___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkFnBody___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = l_Lean_IR_Checker_checkExpr(x_4, x_5, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = l_Lean_IR_LocalContext_contains(x_13, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_IR_LocalContext_addLocal(x_13, x_3, x_4, x_5);
lean_ctor_set(x_2, 1, x_16);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_18; 
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_18 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_22 = l_Lean_IR_LocalContext_contains(x_20, x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_IR_LocalContext_addLocal(x_20, x_3, x_4, x_5);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
x_1 = x_6;
x_2 = x_24;
goto _start;
}
else
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = l_Lean_IR_Checker_checkFnBody___main___closed__2;
return x_26;
}
}
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_32);
x_35 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_28, x_28, x_34, x_32, x_2);
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_2, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_2, 0);
lean_dec(x_39);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_40; 
lean_free_object(x_2);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
lean_inc(x_33);
lean_inc(x_31);
lean_ctor_set(x_2, 1, x_43);
lean_inc(x_29);
x_44 = l_Lean_IR_Checker_checkFnBody___main(x_29, x_2);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_44);
x_48 = l_Lean_IR_LocalContext_contains(x_32, x_27);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_IR_LocalContext_addJP(x_32, x_27, x_28, x_29);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_31);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_33);
x_1 = x_30;
x_2 = x_50;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_52 = l_Lean_IR_Checker_checkFnBody___main___closed__4;
return x_52;
}
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_54 = x_35;
} else {
 lean_dec_ref(x_35);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_35, 0);
lean_inc(x_56);
lean_dec(x_35);
lean_inc(x_33);
lean_inc(x_31);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_33);
lean_inc(x_29);
x_58 = l_Lean_IR_Checker_checkFnBody___main(x_29, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_58);
x_62 = l_Lean_IR_LocalContext_contains(x_32, x_27);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_IR_LocalContext_addJP(x_32, x_27, x_28, x_29);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_31);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_33);
x_1 = x_30;
x_2 = x_64;
goto _start;
}
else
{
lean_object* x_66; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_66 = l_Lean_IR_Checker_checkFnBody___main___closed__4;
return x_66;
}
}
}
}
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 3);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_IR_Checker_checkVar(x_67, x_2);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec(x_70);
x_74 = l_Lean_IR_Checker_checkArg(x_68, x_2);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_69);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_dec(x_74);
x_1 = x_69;
goto _start;
}
}
}
case 4:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 3);
lean_inc(x_81);
lean_dec(x_1);
x_82 = l_Lean_IR_Checker_checkVar(x_79, x_2);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_82);
x_86 = l_Lean_IR_Checker_checkVar(x_80, x_2);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_81);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
return x_86;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
else
{
lean_dec(x_86);
x_1 = x_81;
goto _start;
}
}
}
case 5:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 4);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l_Lean_IR_Checker_checkVar(x_91, x_2);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_94);
x_98 = l_Lean_IR_Checker_checkVar(x_92, x_2);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
lean_dec(x_93);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
lean_dec(x_98);
x_1 = x_93;
goto _start;
}
}
}
case 8:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 1);
lean_inc(x_104);
lean_dec(x_1);
x_105 = l_Lean_IR_Checker_checkVar(x_103, x_2);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
lean_dec(x_104);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
else
{
lean_dec(x_105);
x_1 = x_104;
goto _start;
}
}
case 9:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
lean_dec(x_1);
x_1 = x_110;
goto _start;
}
case 10:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 2);
lean_inc(x_113);
lean_dec(x_1);
x_114 = l_Lean_IR_Checker_checkVar(x_112, x_2);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
lean_dec(x_113);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_114);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_113, x_118, x_2);
lean_dec(x_113);
return x_119;
}
}
case 11:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
lean_dec(x_1);
x_121 = l_Lean_IR_Checker_checkArg(x_120, x_2);
lean_dec(x_2);
return x_121;
}
case 12:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_1, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 1);
lean_inc(x_123);
lean_dec(x_1);
x_124 = l_Lean_IR_Checker_checkJP(x_122, x_2);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
lean_dec(x_123);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_124);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Array_mforAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_123, x_128, x_2);
lean_dec(x_2);
lean_dec(x_123);
return x_129;
}
}
case 13:
{
lean_object* x_130; 
lean_dec(x_2);
x_130 = l_Lean_IR_Checker_checkVar___closed__2;
return x_130;
}
default: 
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 2);
lean_inc(x_132);
lean_dec(x_1);
x_133 = l_Lean_IR_Checker_checkVar(x_131, x_2);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_132);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean_dec(x_133);
x_1 = x_132;
goto _start;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Checker_checkFnBody___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_checkFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2;
return x_16;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_IR_LocalContext_contains(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_9);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_16 = l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2;
return x_16;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__1(x_3, x_3, x_8, x_6, x_2);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_14; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_17);
x_18 = l_Lean_IR_Checker_checkFnBody___main(x_4, x_2);
return x_18;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_20 = x_9;
} else {
 lean_dec_ref(x_9);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_7);
x_24 = l_Lean_IR_Checker_checkFnBody___main(x_4, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__2(x_25, x_25, x_27, x_26, x_2);
lean_dec(x_2);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_28);
x_32 = l_Lean_IR_Checker_checkVar___closed__2;
return x_32;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_Checker_checkDecl___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
lean_object* x_5; 
x_5 = l_Lean_IR_getEnv___rarg(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_inc(x_2);
x_10 = l_Lean_IR_Checker_checkDecl(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_12);
x_15 = l_Lean_IR_checkDecl___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_IR_checkDecl___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_11);
lean_dec(x_11);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_1);
lean_inc(x_2);
x_25 = l_Lean_IR_Checker_checkDecl(x_2, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_27);
x_30 = l_Lean_IR_checkDecl___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_IR_checkDecl___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_26);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_22);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
return x_5;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
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
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
lean_inc(x_1);
x_17 = l_Lean_IR_checkDecl(x_1, x_14, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
x_3 = x_16;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_3 = x_16;
x_5 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
x_5 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_4, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_2, x_3, x_4, x_5);
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
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_CompilerM(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
l_Lean_IR_Checker_checkType___closed__2 = _init_l_Lean_IR_Checker_checkType___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__2);
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
l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1 = _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1();
lean_mark_persistent(l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__1);
l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2 = _init_l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2();
lean_mark_persistent(l_Array_miterateAux___main___at_Lean_IR_Checker_withParams___spec__1___closed__2);
l_Lean_IR_Checker_checkFnBody___main___closed__1 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__1);
l_Lean_IR_Checker_checkFnBody___main___closed__2 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__2);
l_Lean_IR_Checker_checkFnBody___main___closed__3 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__3);
l_Lean_IR_Checker_checkFnBody___main___closed__4 = _init_l_Lean_IR_Checker_checkFnBody___main___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkFnBody___main___closed__4);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__1);
l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__2);
return w;
}
#ifdef __cplusplus
}
#endif
