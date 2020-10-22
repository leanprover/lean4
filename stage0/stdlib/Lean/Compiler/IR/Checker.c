// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: Init Lean.Compiler.IR.CompilerM Lean.Compiler.IR.Format
#include <lean/lean.h>
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
lean_object* l_Lean_IR_Checker_checkFullApp___closed__4;
lean_object* l_Lean_IR_Checker_checkArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP___closed__1;
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4;
lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr_match__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_Checker_markIndex___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_CheckerContext_localCtx___default;
lean_object* l_Lean_IR_Checker_checkExpr___closed__3;
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3;
lean_object* l_Lean_IR_checkDecl_match__1(lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Lean_Compiler_IR_Basic___instance__2___closed__1;
lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr_match__2(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__3;
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___closed__1;
lean_object* l_Lean_IR_Checker_CheckerState_foundVars___default;
lean_object* l_Lean_IR_Checker_checkType___closed__1;
lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArg_match__1(lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecl___closed__2;
lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markIndex___closed__2;
lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
lean_object* l_Lean_IR_Checker_markIndex___closed__1;
lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Lean_Compiler_IR_Basic___instance__6___closed__1;
lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
lean_object* l_Lean_IR_Checker_checkExpr_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
lean_object* l_Lean_IR_Checker_checkExpr_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
lean_object* l_Lean_IR_Checker_checkFnBody_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_getDecl_match__1(lean_object*);
lean_object* l_Lean_IR_checkDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkDecl_match__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l_Lean_IR_Checker_getType_match__1(lean_object*);
lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2;
lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1;
lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Checker_checkFnBody_match__1(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* l_Lean_IR_Checker_markIndex___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_Checker_CheckerContext_localCtx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_CheckerState_foundVars___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_IR_Checker_markIndex___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_1, x_5);
x_7 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable / joinpoint index ");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__2() {
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
x_4 = l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_IR_Checker_markIndex___lambda__1(x_1, x_5, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = l_Nat_repr(x_1);
x_8 = l_Lean_IR_Checker_markIndex___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_markIndex___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_Checker_markIndex___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_markIndex___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
lean_object* l_Lean_IR_Checker_getDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_IR_Checker_getDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl_match__1___rarg), 3, 0);
return x_2;
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
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_1);
x_9 = l_Lean_addClass___closed__1;
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
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__1() {
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
uint8_t x_6; 
x_6 = l_Lean_IR_LocalContext_isParam(x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Nat_repr(x_1);
x_8 = l_Lean_IR_Lean_Compiler_IR_Basic___instance__2___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_checkVar___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
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
static lean_object* _init_l_Lean_IR_Checker_checkJP___closed__1() {
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_isJP(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_Lean_Compiler_IR_Basic___instance__6___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_Checker_checkJP___closed__1;
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
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
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
lean_object* l_Lean_IR_Checker_checkArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_IR_Checker_checkArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkArg_match__1___rarg), 3, 0);
return x_2;
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
x_6 = l_Lean_Compiler_checkIsDefinition___closed__3;
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
x_7 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = l_Lean_IR_Checker_checkArg(x_9, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_19 = x_11;
} else {
 lean_dec_ref(x_11);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
x_4 = x_22;
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
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__2() {
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
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_beq(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
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
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type '");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = lean_apply_1(x_2, x_1);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_Format_pretty(x_7, x_8);
x_10 = l_Lean_IR_Checker_checkType___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
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
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isObj(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = lean_box(0);
x_7 = l_Lean_Format_pretty(x_5, x_6);
x_8 = l_Lean_IR_Checker_checkType___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
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
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isScalar(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = lean_box(0);
x_7 = l_Lean_Format_pretty(x_5, x_6);
x_8 = l_Lean_IR_Checker_checkType___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
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
lean_object* l_Lean_IR_Checker_getType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_IR_Checker_getType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getType_match__1___rarg), 3, 0);
return x_2;
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
x_7 = l_Lean_IR_Lean_Compiler_IR_Basic___instance__2___closed__1;
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
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_apply_1(x_2, x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_20);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Format_pretty(x_23, x_24);
x_26 = l_Lean_IR_Checker_checkType___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Char_HasRepr___closed__1;
x_29 = lean_string_append(x_27, x_28);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_29);
return x_5;
}
else
{
lean_object* x_30; 
lean_free_object(x_6);
lean_dec(x_20);
x_30 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
lean_dec(x_6);
lean_inc(x_31);
x_32 = lean_apply_1(x_2, x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_31);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = l_Lean_Format_pretty(x_34, x_35);
x_37 = l_Lean_IR_Checker_checkType___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Char_HasRepr___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_5, 0, x_41);
return x_5;
}
else
{
lean_object* x_42; 
lean_dec(x_31);
x_42 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_5, 0, x_42);
return x_5;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_ctor_get(x_6, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_45 = x_6;
} else {
 lean_dec_ref(x_6);
 x_45 = lean_box(0);
}
lean_inc(x_44);
x_46 = lean_apply_1(x_2, x_44);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_44);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = l_Lean_Format_pretty(x_48, x_49);
x_51 = l_Lean_IR_Checker_checkType___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Char_HasRepr___closed__1;
x_54 = lean_string_append(x_52, x_53);
if (lean_is_scalar(x_45)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_45;
 lean_ctor_set_tag(x_55, 0);
}
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_44);
x_57 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
return x_58;
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = l_Lean_IR_IRType_isObj(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Format_pretty(x_21, x_22);
x_24 = l_Lean_IR_Checker_checkType___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Char_HasRepr___closed__1;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; 
lean_free_object(x_5);
lean_dec(x_19);
x_28 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = l_Lean_IR_IRType_isObj(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_29);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = l_Lean_Format_pretty(x_31, x_32);
x_34 = l_Lean_IR_Checker_checkType___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Char_HasRepr___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
else
{
lean_object* x_39; 
lean_dec(x_29);
x_39 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_42 = x_5;
} else {
 lean_dec_ref(x_5);
 x_42 = lean_box(0);
}
x_43 = l_Lean_IR_IRType_isObj(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_41);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Lean_Format_pretty(x_44, x_45);
x_47 = l_Lean_IR_Checker_checkType___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Char_HasRepr___closed__1;
x_50 = lean_string_append(x_48, x_49);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_42;
 lean_ctor_set_tag(x_51, 0);
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_42);
lean_dec(x_41);
x_53 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
return x_54;
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = l_Lean_IR_IRType_isScalar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Format_pretty(x_21, x_22);
x_24 = l_Lean_IR_Checker_checkType___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Char_HasRepr___closed__1;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; 
lean_free_object(x_5);
lean_dec(x_19);
x_28 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = l_Lean_IR_IRType_isScalar(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_29);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = l_Lean_Format_pretty(x_31, x_32);
x_34 = l_Lean_IR_Checker_checkType___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Char_HasRepr___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
else
{
lean_object* x_39; 
lean_dec(x_29);
x_39 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_42 = x_5;
} else {
 lean_dec_ref(x_5);
 x_42 = lean_box(0);
}
x_43 = l_Lean_IR_IRType_isScalar(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_41);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Lean_Format_pretty(x_44, x_45);
x_47 = l_Lean_IR_Checker_checkType___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Char_HasRepr___closed__1;
x_50 = lean_string_append(x_48, x_49);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_42;
 lean_ctor_set_tag(x_51, 0);
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_42);
lean_dec(x_41);
x_53 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
return x_54;
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
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incorrect number of arguments to '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', ");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" provided, ");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lean_IR_Checker_getDecl(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_15 = x_7;
} else {
 lean_dec_ref(x_7);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_array_get_size(x_2);
x_24 = l_Lean_IR_Decl_params(x_22);
lean_dec(x_22);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = lean_nat_dec_eq(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = l_System_FilePath_dirName___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Nat_repr(x_23);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Nat_repr(x_25);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4;
x_40 = lean_string_append(x_38, x_39);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_40);
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
lean_dec(x_23);
lean_free_object(x_7);
lean_free_object(x_6);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_41, x_4, x_19);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_array_get_size(x_2);
x_45 = l_Lean_IR_Decl_params(x_43);
lean_dec(x_43);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = lean_nat_dec_eq(x_44, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = l_System_FilePath_dirName___closed__1;
x_49 = l_Lean_Name_toStringWithSep___main(x_48, x_1);
x_50 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Nat_repr(x_44);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = l_Nat_repr(x_46);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_6, 0, x_62);
return x_6;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_46);
lean_dec(x_44);
lean_free_object(x_6);
lean_dec(x_1);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_63, x_4, x_19);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
lean_dec(x_6);
x_66 = lean_ctor_get(x_7, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_67 = x_7;
} else {
 lean_dec_ref(x_7);
 x_67 = lean_box(0);
}
x_68 = lean_array_get_size(x_2);
x_69 = l_Lean_IR_Decl_params(x_66);
lean_dec(x_66);
x_70 = lean_array_get_size(x_69);
lean_dec(x_69);
x_71 = lean_nat_dec_eq(x_68, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = l_System_FilePath_dirName___closed__1;
x_73 = l_Lean_Name_toStringWithSep___main(x_72, x_1);
x_74 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = l_Nat_repr(x_68);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_Nat_repr(x_70);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4;
x_85 = lean_string_append(x_83, x_84);
if (lean_is_scalar(x_67)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_67;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_65);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_1);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_88, x_4, x_65);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hugeFuel");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("the auxiliary constant `hugeFuel` cannot be used in code, it is used internally for compiling `partial` definitions");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_IR_Checker_checkFullApp___lambda__2(x_1, x_2, x_7, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkFullApp___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkFullApp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkFullApp___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments too partial application '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', num. args: ");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = l_System_FilePath_dirName___closed__1;
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
x_38 = l_String_splitAux___main___closed__1;
x_39 = lean_string_append(x_37, x_38);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_39);
return x_5;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_40, x_3, x_18);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_6, 0);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_array_get_size(x_2);
x_44 = l_Lean_IR_Decl_params(x_42);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
lean_dec(x_44);
x_46 = lean_nat_dec_lt(x_43, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = l_System_FilePath_dirName___closed__1;
x_48 = l_Lean_Name_toStringWithSep___main(x_47, x_1);
x_49 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Nat_repr(x_43);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Nat_repr(x_45);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = l_String_splitAux___main___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_5, 0, x_61);
return x_5;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_43);
lean_free_object(x_5);
lean_dec(x_1);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_62, x_3, x_18);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_5, 1);
lean_inc(x_64);
lean_dec(x_5);
x_65 = lean_ctor_get(x_6, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_66 = x_6;
} else {
 lean_dec_ref(x_6);
 x_66 = lean_box(0);
}
x_67 = lean_array_get_size(x_2);
x_68 = l_Lean_IR_Decl_params(x_65);
lean_dec(x_65);
x_69 = lean_array_get_size(x_68);
lean_dec(x_68);
x_70 = lean_nat_dec_lt(x_67, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_71 = l_System_FilePath_dirName___closed__1;
x_72 = l_Lean_Name_toStringWithSep___main(x_71, x_1);
x_73 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_74 = lean_string_append(x_73, x_72);
lean_dec(x_72);
x_75 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_76 = lean_string_append(x_74, x_75);
x_77 = l_Nat_repr(x_67);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
x_79 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Nat_repr(x_69);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
x_83 = l_String_splitAux___main___closed__1;
x_84 = lean_string_append(x_82, x_83);
if (lean_is_scalar(x_66)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_66;
 lean_ctor_set_tag(x_85, 0);
}
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_64);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_2, x_87, x_3, x_64);
return x_88;
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
lean_object* l_Lean_IR_Checker_checkExpr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 8:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 9:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
case 10:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_1(x_6, x_1);
return x_17;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkExpr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkExpr_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_IR_Checker_checkExpr_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_2(x_5, x_17, x_18);
return x_19;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_2(x_6, x_20, x_21);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_box(x_25);
x_28 = lean_apply_4(x_7, x_23, x_24, x_27, x_26);
return x_28;
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_apply_2(x_10, x_29, x_30);
return x_31;
}
case 4:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_apply_2(x_11, x_32, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_apply_3(x_12, x_35, x_36, x_37);
return x_38;
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_apply_2(x_4, x_39, x_40);
return x_41;
}
case 7:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_apply_2(x_2, x_42, x_43);
return x_44;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_apply_2(x_3, x_45, x_46);
return x_47;
}
case 9:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_apply_2(x_8, x_48, x_49);
return x_50;
}
case 10:
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_apply_1(x_9, x_51);
return x_52;
}
case 11:
{
lean_object* x_53; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec(x_15);
x_54 = lean_apply_1(x_16, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_apply_1(x_15, x_55);
return x_56;
}
}
case 12:
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_apply_1(x_13, x_57);
return x_58;
}
default: 
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_apply_1(x_14, x_59);
return x_60;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkExpr_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkExpr_match__2___rarg), 16, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected IR type '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid proj index");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkExpr___closed__2;
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
uint8_t x_9; 
x_9 = l_Lean_IR_CtorInfo_isRef(x_5);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_10, x_3, x_4);
lean_dec(x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_25, x_3, x_24);
lean_dec(x_6);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_27, x_3, x_4);
lean_dec(x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_6, x_29, x_3, x_4);
lean_dec(x_6);
return x_30;
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Lean_IR_Checker_checkObjVar(x_31, x_3, x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
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
lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_44);
return x_45;
}
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Lean_IR_Checker_checkObjVar(x_46, x_3, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_47);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_47, x_61, x_3, x_60);
lean_dec(x_47);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_62, 0, x_68);
return x_62;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_dec(x_62);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_63);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_dec(x_62);
x_75 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_74);
return x_75;
}
}
}
case 3:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
x_78 = l_Lean_IR_Checker_getType(x_77, x_3, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_dec(x_76);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
return x_78;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_78, 0, x_84);
return x_78;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_79, 0);
switch (lean_obj_tag(x_91)) {
case 7:
{
lean_object* x_92; lean_object* x_93; 
lean_free_object(x_79);
lean_dec(x_76);
x_92 = lean_ctor_get(x_78, 1);
lean_inc(x_92);
lean_dec(x_78);
x_93 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_92);
return x_93;
}
case 8:
{
lean_object* x_94; lean_object* x_95; 
lean_free_object(x_79);
lean_dec(x_76);
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_dec(x_78);
x_95 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_94);
return x_95;
}
case 9:
{
uint8_t x_96; 
lean_free_object(x_79);
x_96 = !lean_is_exclusive(x_78);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_78, 0);
lean_dec(x_97);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_99 = lean_array_get_size(x_98);
x_100 = lean_nat_dec_lt(x_76, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_98);
lean_dec(x_76);
x_101 = l_Lean_IR_Checker_checkExpr___closed__3;
lean_ctor_set(x_78, 0, x_101);
return x_78;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_array_fget(x_98, x_76);
lean_dec(x_76);
lean_dec(x_98);
x_103 = l_Lean_IR_IRType_beq(x_102, x_1);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_78, 0, x_104);
return x_78;
}
else
{
lean_object* x_105; 
x_105 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_78, 0, x_105);
return x_78;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_78, 1);
lean_inc(x_106);
lean_dec(x_78);
x_107 = lean_ctor_get(x_91, 1);
lean_inc(x_107);
lean_dec(x_91);
x_108 = lean_array_get_size(x_107);
x_109 = lean_nat_dec_lt(x_76, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_107);
lean_dec(x_76);
x_110 = l_Lean_IR_Checker_checkExpr___closed__3;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_array_fget(x_107, x_76);
lean_dec(x_76);
lean_dec(x_107);
x_113 = l_Lean_IR_IRType_beq(x_112, x_1);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_106);
return x_117;
}
}
}
}
case 10:
{
uint8_t x_118; 
lean_free_object(x_79);
x_118 = !lean_is_exclusive(x_78);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_78, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_91, 1);
lean_inc(x_120);
lean_dec(x_91);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_76, x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_120);
lean_dec(x_76);
x_123 = l_Lean_IR_Checker_checkExpr___closed__3;
lean_ctor_set(x_78, 0, x_123);
return x_78;
}
else
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_array_fget(x_120, x_76);
lean_dec(x_76);
lean_dec(x_120);
x_125 = l_Lean_IR_IRType_beq(x_124, x_1);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_78, 0, x_126);
return x_78;
}
else
{
lean_object* x_127; 
x_127 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_78, 0, x_127);
return x_78;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_78, 1);
lean_inc(x_128);
lean_dec(x_78);
x_129 = lean_ctor_get(x_91, 1);
lean_inc(x_129);
lean_dec(x_91);
x_130 = lean_array_get_size(x_129);
x_131 = lean_nat_dec_lt(x_76, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_129);
lean_dec(x_76);
x_132 = l_Lean_IR_Checker_checkExpr___closed__3;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
else
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_array_fget(x_129, x_76);
lean_dec(x_76);
lean_dec(x_129);
x_135 = l_Lean_IR_IRType_beq(x_134, x_1);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_128);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_128);
return x_139;
}
}
}
}
default: 
{
uint8_t x_140; 
lean_dec(x_76);
x_140 = !lean_is_exclusive(x_78);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_78, 0);
lean_dec(x_141);
x_142 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_91);
lean_dec(x_91);
x_143 = lean_box(0);
x_144 = l_Lean_Format_pretty(x_142, x_143);
x_145 = l_Lean_IR_Checker_checkExpr___closed__1;
x_146 = lean_string_append(x_145, x_144);
lean_dec(x_144);
x_147 = l_Char_HasRepr___closed__1;
x_148 = lean_string_append(x_146, x_147);
lean_ctor_set_tag(x_79, 0);
lean_ctor_set(x_79, 0, x_148);
return x_78;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_149 = lean_ctor_get(x_78, 1);
lean_inc(x_149);
lean_dec(x_78);
x_150 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_91);
lean_dec(x_91);
x_151 = lean_box(0);
x_152 = l_Lean_Format_pretty(x_150, x_151);
x_153 = l_Lean_IR_Checker_checkExpr___closed__1;
x_154 = lean_string_append(x_153, x_152);
lean_dec(x_152);
x_155 = l_Char_HasRepr___closed__1;
x_156 = lean_string_append(x_154, x_155);
lean_ctor_set_tag(x_79, 0);
lean_ctor_set(x_79, 0, x_156);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_79);
lean_ctor_set(x_157, 1, x_149);
return x_157;
}
}
}
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_79, 0);
lean_inc(x_158);
lean_dec(x_79);
switch (lean_obj_tag(x_158)) {
case 7:
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_76);
x_159 = lean_ctor_get(x_78, 1);
lean_inc(x_159);
lean_dec(x_78);
x_160 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_159);
return x_160;
}
case 8:
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_76);
x_161 = lean_ctor_get(x_78, 1);
lean_inc(x_161);
lean_dec(x_78);
x_162 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_161);
return x_162;
}
case 9:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_78, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_164 = x_78;
} else {
 lean_dec_ref(x_78);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
lean_dec(x_158);
x_166 = lean_array_get_size(x_165);
x_167 = lean_nat_dec_lt(x_76, x_166);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_165);
lean_dec(x_76);
x_168 = l_Lean_IR_Checker_checkExpr___closed__3;
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_163);
return x_169;
}
else
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_array_fget(x_165, x_76);
lean_dec(x_76);
lean_dec(x_165);
x_171 = l_Lean_IR_IRType_beq(x_170, x_1);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_164)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_164;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_163);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Lean_Compiler_checkIsDefinition___closed__3;
if (lean_is_scalar(x_164)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_164;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_163);
return x_175;
}
}
}
case 10:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_176 = lean_ctor_get(x_78, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_177 = x_78;
} else {
 lean_dec_ref(x_78);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_158, 1);
lean_inc(x_178);
lean_dec(x_158);
x_179 = lean_array_get_size(x_178);
x_180 = lean_nat_dec_lt(x_76, x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_178);
lean_dec(x_76);
x_181 = l_Lean_IR_Checker_checkExpr___closed__3;
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_176);
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_array_fget(x_178, x_76);
lean_dec(x_76);
lean_dec(x_178);
x_184 = l_Lean_IR_IRType_beq(x_183, x_1);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_177)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_177;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_Lean_Compiler_checkIsDefinition___closed__3;
if (lean_is_scalar(x_177)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_177;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_176);
return x_188;
}
}
}
default: 
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_76);
x_189 = lean_ctor_get(x_78, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_190 = x_78;
} else {
 lean_dec_ref(x_78);
 x_190 = lean_box(0);
}
x_191 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_158);
lean_dec(x_158);
x_192 = lean_box(0);
x_193 = l_Lean_Format_pretty(x_191, x_192);
x_194 = l_Lean_IR_Checker_checkExpr___closed__1;
x_195 = lean_string_append(x_194, x_193);
lean_dec(x_193);
x_196 = l_Char_HasRepr___closed__1;
x_197 = lean_string_append(x_195, x_196);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
if (lean_is_scalar(x_190)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_190;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_189);
return x_199;
}
}
}
}
}
case 4:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_2, 1);
lean_inc(x_200);
lean_dec(x_2);
x_201 = l_Lean_IR_Checker_checkObjVar(x_200, x_3, x_4);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_201);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_202);
if (x_205 == 0)
{
return x_201;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
lean_dec(x_202);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_201, 0, x_207);
return x_201;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
lean_dec(x_201);
x_209 = lean_ctor_get(x_202, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_210 = x_202;
} else {
 lean_dec_ref(x_202);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_208);
return x_212;
}
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_202);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_202, 0);
lean_dec(x_214);
x_215 = !lean_is_exclusive(x_201);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = lean_ctor_get(x_201, 0);
lean_dec(x_216);
x_217 = lean_box(5);
x_218 = l_Lean_IR_IRType_beq(x_1, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_220 = lean_box(0);
x_221 = l_Lean_Format_pretty(x_219, x_220);
x_222 = l_Lean_IR_Checker_checkType___closed__1;
x_223 = lean_string_append(x_222, x_221);
lean_dec(x_221);
x_224 = l_Char_HasRepr___closed__1;
x_225 = lean_string_append(x_223, x_224);
lean_ctor_set_tag(x_202, 0);
lean_ctor_set(x_202, 0, x_225);
return x_201;
}
else
{
lean_object* x_226; 
lean_free_object(x_202);
x_226 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_201, 0, x_226);
return x_201;
}
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_227 = lean_ctor_get(x_201, 1);
lean_inc(x_227);
lean_dec(x_201);
x_228 = lean_box(5);
x_229 = l_Lean_IR_IRType_beq(x_1, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_230 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_231 = lean_box(0);
x_232 = l_Lean_Format_pretty(x_230, x_231);
x_233 = l_Lean_IR_Checker_checkType___closed__1;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Char_HasRepr___closed__1;
x_236 = lean_string_append(x_234, x_235);
lean_ctor_set_tag(x_202, 0);
lean_ctor_set(x_202, 0, x_236);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_202);
lean_ctor_set(x_237, 1, x_227);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_free_object(x_202);
x_238 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_227);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
lean_dec(x_202);
x_240 = lean_ctor_get(x_201, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_241 = x_201;
} else {
 lean_dec_ref(x_201);
 x_241 = lean_box(0);
}
x_242 = lean_box(5);
x_243 = l_Lean_IR_IRType_beq(x_1, x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_244 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_245 = lean_box(0);
x_246 = l_Lean_Format_pretty(x_244, x_245);
x_247 = l_Lean_IR_Checker_checkType___closed__1;
x_248 = lean_string_append(x_247, x_246);
lean_dec(x_246);
x_249 = l_Char_HasRepr___closed__1;
x_250 = lean_string_append(x_248, x_249);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_250);
if (lean_is_scalar(x_241)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_241;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_240);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = l_Lean_Compiler_checkIsDefinition___closed__3;
if (lean_is_scalar(x_241)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_241;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_240);
return x_254;
}
}
}
}
case 5:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_2, 2);
lean_inc(x_255);
lean_dec(x_2);
x_256 = l_Lean_IR_Checker_checkObjVar(x_255, x_3, x_4);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_256);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_256, 0);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_257);
if (x_260 == 0)
{
return x_256;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_257, 0);
lean_inc(x_261);
lean_dec(x_257);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_256, 0, x_262);
return x_256;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_256, 1);
lean_inc(x_263);
lean_dec(x_256);
x_264 = lean_ctor_get(x_257, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_265 = x_257;
} else {
 lean_dec_ref(x_257);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 1, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_264);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_263);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_257);
x_268 = lean_ctor_get(x_256, 1);
lean_inc(x_268);
lean_dec(x_256);
x_269 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_268);
return x_269;
}
}
case 6:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_2, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_2, 1);
lean_inc(x_271);
lean_dec(x_2);
x_272 = l_Lean_IR_Checker_checkFullApp(x_270, x_271, x_3, x_4);
lean_dec(x_271);
return x_272;
}
case 7:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_2, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_2, 1);
lean_inc(x_274);
lean_dec(x_2);
x_275 = l_Lean_IR_Checker_checkPartialApp(x_273, x_274, x_3, x_4);
lean_dec(x_274);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_275);
if (x_277 == 0)
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_ctor_get(x_275, 0);
lean_dec(x_278);
x_279 = !lean_is_exclusive(x_276);
if (x_279 == 0)
{
return x_275;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
lean_dec(x_276);
x_281 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_275, 0, x_281);
return x_275;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_275, 1);
lean_inc(x_282);
lean_dec(x_275);
x_283 = lean_ctor_get(x_276, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 x_284 = x_276;
} else {
 lean_dec_ref(x_276);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 1, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_283);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_282);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_276);
x_287 = lean_ctor_get(x_275, 1);
lean_inc(x_287);
lean_dec(x_275);
x_288 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_287);
return x_288;
}
}
case 8:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_2, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_2, 1);
lean_inc(x_290);
lean_dec(x_2);
x_291 = l_Lean_IR_Checker_checkObjVar(x_289, x_3, x_4);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_obj_tag(x_292) == 0)
{
uint8_t x_293; 
lean_dec(x_290);
x_293 = !lean_is_exclusive(x_291);
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; 
x_294 = lean_ctor_get(x_291, 0);
lean_dec(x_294);
x_295 = !lean_is_exclusive(x_292);
if (x_295 == 0)
{
return x_291;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
lean_dec(x_292);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_291, 0, x_297);
return x_291;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_291, 1);
lean_inc(x_298);
lean_dec(x_291);
x_299 = lean_ctor_get(x_292, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_300 = x_292;
} else {
 lean_dec_ref(x_292);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_298);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_292);
x_303 = lean_ctor_get(x_291, 1);
lean_inc(x_303);
lean_dec(x_291);
x_304 = lean_unsigned_to_nat(0u);
x_305 = l_Array_forMAux___main___at_Lean_IR_Checker_checkArgs___spec__1(x_290, x_304, x_3, x_303);
lean_dec(x_290);
return x_305;
}
}
case 9:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_2, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_2, 1);
lean_inc(x_307);
lean_dec(x_2);
x_308 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 0)
{
uint8_t x_310; 
lean_dec(x_307);
lean_dec(x_306);
x_310 = !lean_is_exclusive(x_308);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_308, 0);
lean_dec(x_311);
x_312 = !lean_is_exclusive(x_309);
if (x_312 == 0)
{
return x_308;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_309, 0);
lean_inc(x_313);
lean_dec(x_309);
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_308, 0, x_314);
return x_308;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_308, 1);
lean_inc(x_315);
lean_dec(x_308);
x_316 = lean_ctor_get(x_309, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_317 = x_309;
} else {
 lean_dec_ref(x_309);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_315);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_309);
x_320 = lean_ctor_get(x_308, 1);
lean_inc(x_320);
lean_dec(x_308);
lean_inc(x_307);
x_321 = l_Lean_IR_Checker_checkScalarVar(x_307, x_3, x_320);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 0)
{
uint8_t x_323; 
lean_dec(x_307);
lean_dec(x_306);
x_323 = !lean_is_exclusive(x_321);
if (x_323 == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_321, 0);
lean_dec(x_324);
x_325 = !lean_is_exclusive(x_322);
if (x_325 == 0)
{
return x_321;
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
lean_dec(x_322);
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_321, 0, x_327);
return x_321;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_328 = lean_ctor_get(x_321, 1);
lean_inc(x_328);
lean_dec(x_321);
x_329 = lean_ctor_get(x_322, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_330 = x_322;
} else {
 lean_dec_ref(x_322);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_328);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_322);
x_333 = lean_ctor_get(x_321, 1);
lean_inc(x_333);
lean_dec(x_321);
x_334 = l_Lean_IR_Checker_getType(x_307, x_3, x_333);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
if (lean_obj_tag(x_335) == 0)
{
uint8_t x_336; 
lean_dec(x_306);
x_336 = !lean_is_exclusive(x_334);
if (x_336 == 0)
{
lean_object* x_337; uint8_t x_338; 
x_337 = lean_ctor_get(x_334, 0);
lean_dec(x_337);
x_338 = !lean_is_exclusive(x_335);
if (x_338 == 0)
{
return x_334;
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_335, 0);
lean_inc(x_339);
lean_dec(x_335);
x_340 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_334, 0, x_340);
return x_334;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_334, 1);
lean_inc(x_341);
lean_dec(x_334);
x_342 = lean_ctor_get(x_335, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_343 = x_335;
} else {
 lean_dec_ref(x_335);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_341);
return x_345;
}
}
else
{
uint8_t x_346; 
x_346 = !lean_is_exclusive(x_334);
if (x_346 == 0)
{
lean_object* x_347; uint8_t x_348; 
x_347 = lean_ctor_get(x_334, 0);
lean_dec(x_347);
x_348 = !lean_is_exclusive(x_335);
if (x_348 == 0)
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_ctor_get(x_335, 0);
x_350 = l_Lean_IR_IRType_beq(x_349, x_306);
lean_dec(x_306);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_351 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_349);
lean_dec(x_349);
x_352 = lean_box(0);
x_353 = l_Lean_Format_pretty(x_351, x_352);
x_354 = l_Lean_IR_Checker_checkType___closed__1;
x_355 = lean_string_append(x_354, x_353);
lean_dec(x_353);
x_356 = l_Char_HasRepr___closed__1;
x_357 = lean_string_append(x_355, x_356);
lean_ctor_set_tag(x_335, 0);
lean_ctor_set(x_335, 0, x_357);
return x_334;
}
else
{
lean_object* x_358; 
lean_free_object(x_335);
lean_dec(x_349);
x_358 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_334, 0, x_358);
return x_334;
}
}
else
{
lean_object* x_359; uint8_t x_360; 
x_359 = lean_ctor_get(x_335, 0);
lean_inc(x_359);
lean_dec(x_335);
x_360 = l_Lean_IR_IRType_beq(x_359, x_306);
lean_dec(x_306);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_361 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_359);
lean_dec(x_359);
x_362 = lean_box(0);
x_363 = l_Lean_Format_pretty(x_361, x_362);
x_364 = l_Lean_IR_Checker_checkType___closed__1;
x_365 = lean_string_append(x_364, x_363);
lean_dec(x_363);
x_366 = l_Char_HasRepr___closed__1;
x_367 = lean_string_append(x_365, x_366);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_334, 0, x_368);
return x_334;
}
else
{
lean_object* x_369; 
lean_dec(x_359);
x_369 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_334, 0, x_369);
return x_334;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_370 = lean_ctor_get(x_334, 1);
lean_inc(x_370);
lean_dec(x_334);
x_371 = lean_ctor_get(x_335, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_372 = x_335;
} else {
 lean_dec_ref(x_335);
 x_372 = lean_box(0);
}
x_373 = l_Lean_IR_IRType_beq(x_371, x_306);
lean_dec(x_306);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_374 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_371);
lean_dec(x_371);
x_375 = lean_box(0);
x_376 = l_Lean_Format_pretty(x_374, x_375);
x_377 = l_Lean_IR_Checker_checkType___closed__1;
x_378 = lean_string_append(x_377, x_376);
lean_dec(x_376);
x_379 = l_Char_HasRepr___closed__1;
x_380 = lean_string_append(x_378, x_379);
if (lean_is_scalar(x_372)) {
 x_381 = lean_alloc_ctor(0, 1, 0);
} else {
 x_381 = x_372;
 lean_ctor_set_tag(x_381, 0);
}
lean_ctor_set(x_381, 0, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_370);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; 
lean_dec(x_372);
lean_dec(x_371);
x_383 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_370);
return x_384;
}
}
}
}
}
}
case 10:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_2, 0);
lean_inc(x_385);
lean_dec(x_2);
x_386 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
if (lean_obj_tag(x_387) == 0)
{
uint8_t x_388; 
lean_dec(x_385);
x_388 = !lean_is_exclusive(x_386);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_386, 0);
lean_dec(x_389);
x_390 = !lean_is_exclusive(x_387);
if (x_390 == 0)
{
return x_386;
}
else
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_387, 0);
lean_inc(x_391);
lean_dec(x_387);
x_392 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_386, 0, x_392);
return x_386;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_393 = lean_ctor_get(x_386, 1);
lean_inc(x_393);
lean_dec(x_386);
x_394 = lean_ctor_get(x_387, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_395 = x_387;
} else {
 lean_dec_ref(x_387);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(0, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_393);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_387);
x_398 = lean_ctor_get(x_386, 1);
lean_inc(x_398);
lean_dec(x_386);
x_399 = l_Lean_IR_Checker_checkObjVar(x_385, x_3, x_398);
return x_399;
}
}
case 11:
{
lean_object* x_400; 
x_400 = lean_ctor_get(x_2, 0);
lean_inc(x_400);
lean_dec(x_2);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_400);
x_401 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_4);
return x_402;
}
else
{
lean_object* x_403; 
lean_dec(x_400);
x_403 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
return x_403;
}
}
default: 
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_2, 0);
lean_inc(x_404);
lean_dec(x_2);
x_405 = l_Lean_IR_Checker_checkObjVar(x_404, x_3, x_4);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
if (lean_obj_tag(x_406) == 0)
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_405);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_ctor_get(x_405, 0);
lean_dec(x_408);
x_409 = !lean_is_exclusive(x_406);
if (x_409 == 0)
{
return x_405;
}
else
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_406, 0);
lean_inc(x_410);
lean_dec(x_406);
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_405, 0, x_411);
return x_405;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_412 = lean_ctor_get(x_405, 1);
lean_inc(x_412);
lean_dec(x_405);
x_413 = lean_ctor_get(x_406, 0);
lean_inc(x_413);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_414 = x_406;
} else {
 lean_dec_ref(x_406);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(0, 1, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_413);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_412);
return x_416;
}
}
else
{
uint8_t x_417; 
x_417 = !lean_is_exclusive(x_406);
if (x_417 == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = lean_ctor_get(x_406, 0);
lean_dec(x_418);
x_419 = !lean_is_exclusive(x_405);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_420 = lean_ctor_get(x_405, 0);
lean_dec(x_420);
x_421 = lean_box(1);
x_422 = l_Lean_IR_IRType_beq(x_1, x_421);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_423 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_424 = lean_box(0);
x_425 = l_Lean_Format_pretty(x_423, x_424);
x_426 = l_Lean_IR_Checker_checkType___closed__1;
x_427 = lean_string_append(x_426, x_425);
lean_dec(x_425);
x_428 = l_Char_HasRepr___closed__1;
x_429 = lean_string_append(x_427, x_428);
lean_ctor_set_tag(x_406, 0);
lean_ctor_set(x_406, 0, x_429);
return x_405;
}
else
{
lean_object* x_430; 
lean_free_object(x_406);
x_430 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_405, 0, x_430);
return x_405;
}
}
else
{
lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_431 = lean_ctor_get(x_405, 1);
lean_inc(x_431);
lean_dec(x_405);
x_432 = lean_box(1);
x_433 = l_Lean_IR_IRType_beq(x_1, x_432);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_434 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_435 = lean_box(0);
x_436 = l_Lean_Format_pretty(x_434, x_435);
x_437 = l_Lean_IR_Checker_checkType___closed__1;
x_438 = lean_string_append(x_437, x_436);
lean_dec(x_436);
x_439 = l_Char_HasRepr___closed__1;
x_440 = lean_string_append(x_438, x_439);
lean_ctor_set_tag(x_406, 0);
lean_ctor_set(x_406, 0, x_440);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_406);
lean_ctor_set(x_441, 1, x_431);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; 
lean_free_object(x_406);
x_442 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_431);
return x_443;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
lean_dec(x_406);
x_444 = lean_ctor_get(x_405, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_445 = x_405;
} else {
 lean_dec_ref(x_405);
 x_445 = lean_box(0);
}
x_446 = lean_box(1);
x_447 = l_Lean_IR_IRType_beq(x_1, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_448 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_449 = lean_box(0);
x_450 = l_Lean_Format_pretty(x_448, x_449);
x_451 = l_Lean_IR_Checker_checkType___closed__1;
x_452 = lean_string_append(x_451, x_450);
lean_dec(x_450);
x_453 = l_Char_HasRepr___closed__1;
x_454 = lean_string_append(x_452, x_453);
x_455 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_455, 0, x_454);
if (lean_is_scalar(x_445)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_445;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_444);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; 
x_457 = l_Lean_Compiler_checkIsDefinition___closed__3;
if (lean_is_scalar(x_445)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_445;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_444);
return x_458;
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
lean_object* l_Lean_IR_Checker_checkFnBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_2, x_16, x_17, x_18, x_19);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_apply_4(x_3, x_21, x_22, x_23, x_24);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_4(x_4, x_26, x_27, x_28, x_29);
return x_30;
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_apply_3(x_7, x_31, x_32, x_33);
return x_34;
}
case 4:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_apply_4(x_5, x_35, x_36, x_37, x_38);
return x_39;
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_apply_6(x_6, x_40, x_41, x_42, x_43, x_44, x_45);
return x_46;
}
case 6:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_50 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_box(x_49);
x_53 = lean_box(x_50);
x_54 = lean_apply_5(x_8, x_47, x_48, x_52, x_53, x_51);
return x_54;
}
case 7:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_box(x_57);
x_61 = lean_box(x_58);
x_62 = lean_apply_5(x_9, x_55, x_56, x_60, x_61, x_59);
return x_62;
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_apply_2(x_10, x_63, x_64);
return x_65;
}
case 9:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_apply_2(x_11, x_66, x_67);
return x_68;
}
case 10:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
lean_dec(x_1);
x_73 = lean_apply_4(x_14, x_69, x_70, x_71, x_72);
return x_73;
}
case 11:
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_apply_1(x_13, x_74);
return x_75;
}
case 12:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
lean_dec(x_1);
x_78 = lean_apply_2(x_12, x_76, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_apply_1(x_15, x_79);
return x_80;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkFnBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkFnBody_match__1___rarg), 15, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = l_Lean_IR_AltCore_body(x_9);
lean_dec(x_9);
lean_inc(x_3);
x_11 = l_Lean_IR_Checker_checkFnBody(x_10, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_20 = x_12;
} else {
 lean_dec_ref(x_12);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_4 = x_23;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_65 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___spec__1(x_45, x_45, x_64, x_62, x_2, x_60);
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
x_83 = l_Lean_IR_Checker_checkFnBody(x_46, x_2, x_81);
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
x_109 = l_Lean_IR_Checker_checkFnBody(x_46, x_108, x_106);
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
x_245 = l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___spec__2(x_230, x_244, x_2, x_243);
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
x_265 = l_Lean_Compiler_checkIsDefinition___closed__3;
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
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_IR_Checker_checkFnBody___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Checker_checkFnBody___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Checker_checkDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_4(x_3, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_IR_Checker_checkDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkDecl_match__1___rarg), 3, 0);
return x_2;
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
x_28 = l_Lean_IR_Checker_checkFnBody(x_5, x_2, x_26);
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
x_39 = l_Lean_IR_Checker_checkFnBody(x_5, x_38, x_36);
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
x_57 = l_Lean_Compiler_checkIsDefinition___closed__3;
lean_ctor_set(x_43, 0, x_57);
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
x_59 = l_Lean_Compiler_checkIsDefinition___closed__3;
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
lean_object* l_Lean_IR_checkDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_IR_checkDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_checkDecl_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IR check failed at '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__2() {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = l_Lean_IR_checkDecl___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_checkDecl___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_12);
lean_dec(x_12);
x_21 = l_String_splitAux___main___closed__1;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_1);
lean_inc(x_2);
x_28 = l_Lean_IR_Checker_checkDecl(x_2, x_27, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_32 = l_System_FilePath_dirName___closed__1;
x_33 = l_Lean_Name_toStringWithSep___main(x_32, x_31);
x_34 = l_Lean_IR_checkDecl___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_IR_checkDecl___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_30);
lean_dec(x_30);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_25);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_25);
return x_43;
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_11 = l_Lean_IR_checkDecl(x_1, x_10, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_Checker(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Checker_CheckerContext_localCtx___default = _init_l_Lean_IR_Checker_CheckerContext_localCtx___default();
lean_mark_persistent(l_Lean_IR_Checker_CheckerContext_localCtx___default);
l_Lean_IR_Checker_CheckerState_foundVars___default = _init_l_Lean_IR_Checker_CheckerState_foundVars___default();
lean_mark_persistent(l_Lean_IR_Checker_CheckerState_foundVars___default);
l_Lean_IR_Checker_markIndex___closed__1 = _init_l_Lean_IR_Checker_markIndex___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__1);
l_Lean_IR_Checker_markIndex___closed__2 = _init_l_Lean_IR_Checker_markIndex___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__2);
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
l_Lean_IR_Checker_checkEqTypes___closed__1 = _init_l_Lean_IR_Checker_checkEqTypes___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__1);
l_Lean_IR_Checker_checkEqTypes___closed__2 = _init_l_Lean_IR_Checker_checkEqTypes___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__2);
l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1 = _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___lambda__2___closed__1);
l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2 = _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___lambda__2___closed__2);
l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3 = _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___lambda__2___closed__3);
l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4 = _init_l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___lambda__2___closed__4);
l_Lean_IR_Checker_checkFullApp___closed__1 = _init_l_Lean_IR_Checker_checkFullApp___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__1);
l_Lean_IR_Checker_checkFullApp___closed__2 = _init_l_Lean_IR_Checker_checkFullApp___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__2);
l_Lean_IR_Checker_checkFullApp___closed__3 = _init_l_Lean_IR_Checker_checkFullApp___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__3);
l_Lean_IR_Checker_checkFullApp___closed__4 = _init_l_Lean_IR_Checker_checkFullApp___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__4);
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
l_Lean_IR_Checker_checkExpr___closed__3 = _init_l_Lean_IR_Checker_checkExpr___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__3);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__1);
l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
