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
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_IR_Checker_getDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
lean_object* l_Lean_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__4;
lean_object* lean_get_max_ctor_fields(lean_object*);
lean_object* lean_get_max_ctor_tag(lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
static lean_object* l_Lean_IR_Checker_checkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerState_foundVars___default;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__4;
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_usizeSize___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkObjType___closed__1;
static lean_object* l_Lean_IR_Checker_checkExpr___lambda__3___closed__1;
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__2;
static lean_object* l_Lean_IR_Checker_markIndex___closed__2;
static lean_object* l_Lean_IR_Checker_maxCtorScalarsSize___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__1;
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___closed__1;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorTag;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorTag___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_checkDecl___closed__1;
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerContext_localCtx___default;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkScalarType___closed__1;
static lean_object* l_Lean_IR_checkDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_maxCtorFields___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_maxCtorScalarsSize___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_maxCtorTag___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_usizeSize___closed__1;
return x_1;
}
}
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
static lean_object* _init_l_Lean_IR_Checker_markIndex___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_1, x_5);
x_7 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_1 = lean_mk_string_from_bytes("variable / joinpoint index ", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" has already been used", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_IR_Checker_markIndex___lambda__1(x_1, x_5, x_2, x_3);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_markIndex___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown declaration '", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = 1;
x_8 = l_Lean_Name_toString(x_1, x_7);
x_9 = l_Lean_IR_Checker_getDecl___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_getDecl___closed__2;
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
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x_", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown variable '", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_IR_Checker_checkVar___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_checkVar___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_16 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_18 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_mk_string_from_bytes("block_", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkJP___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown join point '", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_isJP(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_Checker_checkJP___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_Checker_checkJP___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_15 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_Checker_checkArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_18 = x_10;
} else {
 lean_dec_ref(x_10);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_22;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_12, x_13, x_14, x_2, x_3);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected type '{ty₁}' != '{ty₂}'", 38);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected type '", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkType___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_6 = lean_apply_1(x_2, x_1);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_9 = l_Std_Format_defWidth;
x_10 = lean_format_pretty(x_8, x_9);
x_11 = l_Lean_IR_Checker_checkType___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_Checker_getDecl___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_IR_Checker_checkType___closed__2;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_apply_4(x_15, x_14, x_16, x_4, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = l_Lean_IR_Checker_checkType___closed__3;
x_20 = lean_string_append(x_19, x_14);
lean_dec(x_14);
x_21 = l_Lean_IR_Checker_checkType___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_18);
x_24 = lean_string_append(x_23, x_19);
x_25 = lean_box(0);
x_26 = lean_apply_4(x_15, x_24, x_25, x_4, x_5);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_1);
x_27 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkType___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkObjType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("object expected", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isObj(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = l_Std_Format_defWidth;
x_7 = lean_format_pretty(x_5, x_6);
x_8 = l_Lean_IR_Checker_checkType___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_getDecl___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_Checker_checkType___closed__2;
x_13 = l_Lean_IR_Checker_checkType___closed__3;
x_14 = lean_string_append(x_13, x_11);
lean_dec(x_11);
x_15 = l_Lean_IR_Checker_checkType___closed__4;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_checkObjType___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = lean_box(0);
x_21 = lean_apply_4(x_12, x_19, x_20, x_2, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkScalarType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("scalar expected", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isScalar(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = l_Std_Format_defWidth;
x_7 = lean_format_pretty(x_5, x_6);
x_8 = l_Lean_IR_Checker_checkType___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_getDecl___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_Checker_checkType___closed__2;
x_13 = l_Lean_IR_Checker_checkType___closed__3;
x_14 = lean_string_append(x_13, x_11);
lean_dec(x_11);
x_15 = l_Lean_IR_Checker_checkType___closed__4;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_checkScalarType___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = lean_box(0);
x_21 = lean_apply_4(x_12, x_19, x_20, x_2, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_getType(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_Checker_checkVar___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_Checker_checkVar___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_getDecl___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_Checker_getType(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
lean_inc(x_21);
x_22 = lean_apply_1(x_2, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_6);
x_24 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_21);
x_25 = l_Std_Format_defWidth;
x_26 = lean_format_pretty(x_24, x_25);
x_27 = l_Lean_IR_Checker_checkType___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_IR_Checker_getDecl___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lean_IR_Checker_checkType___closed__2;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = lean_apply_4(x_31, x_30, x_32, x_4, x_19);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = l_Lean_IR_Checker_checkType___closed__3;
x_36 = lean_string_append(x_35, x_30);
lean_dec(x_30);
x_37 = l_Lean_IR_Checker_checkType___closed__4;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_34);
x_40 = lean_string_append(x_39, x_35);
x_41 = lean_box(0);
x_42 = lean_apply_4(x_31, x_40, x_41, x_4, x_19);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_21);
lean_dec(x_4);
x_43 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_6, 0, x_43);
return x_6;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
lean_dec(x_7);
lean_inc(x_45);
x_46 = lean_apply_1(x_2, x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_45);
x_49 = l_Std_Format_defWidth;
x_50 = lean_format_pretty(x_48, x_49);
x_51 = l_Lean_IR_Checker_checkType___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_IR_Checker_getDecl___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Lean_IR_Checker_checkType___closed__2;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = lean_apply_4(x_55, x_54, x_56, x_4, x_44);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_3, 0);
x_59 = l_Lean_IR_Checker_checkType___closed__3;
x_60 = lean_string_append(x_59, x_54);
lean_dec(x_54);
x_61 = l_Lean_IR_Checker_checkType___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_58);
x_64 = lean_string_append(x_63, x_59);
x_65 = lean_box(0);
x_66 = lean_apply_4(x_55, x_64, x_65, x_4, x_44);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_45);
lean_dec(x_4);
x_67 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_44);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Lean_IR_IRType_isObj(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_4);
x_21 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_22 = l_Std_Format_defWidth;
x_23 = lean_format_pretty(x_21, x_22);
x_24 = l_Lean_IR_Checker_checkType___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_IR_Checker_getDecl___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_Checker_checkType___closed__2;
x_29 = l_Lean_IR_Checker_checkType___closed__3;
x_30 = lean_string_append(x_29, x_27);
lean_dec(x_27);
x_31 = l_Lean_IR_Checker_checkType___closed__4;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_IR_Checker_checkObjType___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_29);
x_36 = lean_box(0);
x_37 = lean_apply_4(x_28, x_35, x_36, x_2, x_17);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_2);
x_38 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
lean_dec(x_5);
x_41 = l_Lean_IR_IRType_isObj(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_40);
x_43 = l_Std_Format_defWidth;
x_44 = lean_format_pretty(x_42, x_43);
x_45 = l_Lean_IR_Checker_checkType___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_IR_Checker_getDecl___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_Lean_IR_Checker_checkType___closed__2;
x_50 = l_Lean_IR_Checker_checkType___closed__3;
x_51 = lean_string_append(x_50, x_48);
lean_dec(x_48);
x_52 = l_Lean_IR_Checker_checkType___closed__4;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lean_IR_Checker_checkObjType___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_50);
x_57 = lean_box(0);
x_58 = lean_apply_4(x_49, x_56, x_57, x_2, x_39);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_40);
lean_dec(x_2);
x_59 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_39);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Lean_IR_IRType_isScalar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_4);
x_21 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_22 = l_Std_Format_defWidth;
x_23 = lean_format_pretty(x_21, x_22);
x_24 = l_Lean_IR_Checker_checkType___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_IR_Checker_getDecl___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_Checker_checkType___closed__2;
x_29 = l_Lean_IR_Checker_checkType___closed__3;
x_30 = lean_string_append(x_29, x_27);
lean_dec(x_27);
x_31 = l_Lean_IR_Checker_checkType___closed__4;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_IR_Checker_checkScalarType___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_29);
x_36 = lean_box(0);
x_37 = lean_apply_4(x_28, x_35, x_36, x_2, x_17);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_2);
x_38 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
lean_dec(x_5);
x_41 = l_Lean_IR_IRType_isScalar(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_40);
x_43 = l_Std_Format_defWidth;
x_44 = lean_format_pretty(x_42, x_43);
x_45 = l_Lean_IR_Checker_checkType___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_IR_Checker_getDecl___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_Lean_IR_Checker_checkType___closed__2;
x_50 = l_Lean_IR_Checker_checkType___closed__3;
x_51 = lean_string_append(x_50, x_48);
lean_dec(x_48);
x_52 = l_Lean_IR_Checker_checkType___closed__4;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lean_IR_Checker_checkScalarType___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_50);
x_57 = lean_box(0);
x_58 = lean_apply_4(x_49, x_56, x_57, x_2, x_39);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_40);
lean_dec(x_2);
x_59 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_39);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkArgs(x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("incorrect number of arguments to '", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" provided, ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" expected", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
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
x_25 = lean_nat_dec_eq(x_22, x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_1, x_26);
x_28 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_repr(x_22);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Nat_repr(x_24);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_39 = lean_string_append(x_37, x_38);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_39);
return x_5;
}
else
{
lean_object* x_40; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_40 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_array_get_size(x_2);
x_43 = l_Lean_IR_Decl_params(x_41);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_nat_dec_eq(x_42, x_44);
if (x_45 == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_46 = 1;
x_47 = l_Lean_Name_toString(x_1, x_46);
x_48 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Nat_repr(x_42);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Nat_repr(x_44);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_5, 0, x_60);
return x_5;
}
else
{
lean_object* x_61; 
lean_dec(x_44);
lean_dec(x_42);
lean_free_object(x_5);
lean_dec(x_1);
x_61 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_ctor_get(x_6, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = lean_array_get_size(x_2);
x_66 = l_Lean_IR_Decl_params(x_63);
lean_dec(x_63);
x_67 = lean_array_get_size(x_66);
lean_dec(x_66);
x_68 = lean_nat_dec_eq(x_65, x_67);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_69 = 1;
x_70 = l_Lean_Name_toString(x_1, x_69);
x_71 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_Nat_repr(x_65);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_Nat_repr(x_67);
x_80 = lean_string_append(x_78, x_79);
lean_dec(x_79);
x_81 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_82 = lean_string_append(x_80, x_81);
if (lean_is_scalar(x_64)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_64;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_62);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_85 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_62);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkFullApp___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("too many arguments too partial application '", 44);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', num. args: ", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", arity: ", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
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
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_1, x_26);
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
x_38 = l_Lean_IR_Checker_checkType___closed__3;
x_39 = lean_string_append(x_37, x_38);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_39);
return x_5;
}
else
{
lean_object* x_40; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_40 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_array_get_size(x_2);
x_43 = l_Lean_IR_Decl_params(x_41);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_nat_dec_lt(x_42, x_44);
if (x_45 == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_46 = 1;
x_47 = l_Lean_Name_toString(x_1, x_46);
x_48 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Nat_repr(x_42);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Nat_repr(x_44);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = l_Lean_IR_Checker_checkType___closed__3;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_5, 0, x_60);
return x_5;
}
else
{
lean_object* x_61; 
lean_dec(x_44);
lean_dec(x_42);
lean_free_object(x_5);
lean_dec(x_1);
x_61 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_ctor_get(x_6, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = lean_array_get_size(x_2);
x_66 = l_Lean_IR_Decl_params(x_63);
lean_dec(x_63);
x_67 = lean_array_get_size(x_66);
lean_dec(x_66);
x_68 = lean_nat_dec_lt(x_65, x_67);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_69 = 1;
x_70 = l_Lean_Name_toString(x_1, x_69);
x_71 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_Nat_repr(x_65);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_Nat_repr(x_67);
x_80 = lean_string_append(x_78, x_79);
lean_dec(x_79);
x_81 = l_Lean_IR_Checker_checkType___closed__3;
x_82 = lean_string_append(x_80, x_81);
if (lean_is_scalar(x_64)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_64;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_62);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_85 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_62);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isStruct(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_IR_IRType_isUnion(x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_IR_CtorInfo_isRef(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_12 = l_Lean_IR_Checker_checkObjType(x_1, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_5);
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
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = l_Lean_IR_Checker_checkArgs(x_3, x_5, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_1);
x_26 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_1);
x_28 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("constructor '", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has too many scalar fields", 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = l_Lean_IR_Checker_usizeSize;
x_10 = lean_nat_mul(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_12 = l_Lean_IR_Checker_maxCtorScalarsSize;
x_13 = lean_nat_dec_lt(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_IR_Checker_checkExpr___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6);
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = 1;
x_18 = l_Lean_Name_toString(x_16, x_17);
x_19 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has too many fields", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = l_Lean_IR_Checker_maxCtorFields;
x_9 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_IR_Checker_checkExpr___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_12, x_13);
x_15 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_IR_Checker_checkExpr___lambda__3___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tag for constructor '", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is too big, this is a limitation of the current runtime", 57);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected IR type '", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid proj index", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkExpr___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
x_19 = l_Lean_IR_Checker_maxCtorTag;
x_20 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_IR_Checker_checkExpr___lambda__3(x_1, x_5, x_6, x_21, x_3, x_4);
lean_dec(x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_5, 3);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_24, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_5, 4);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_24, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_IR_Checker_checkExpr___lambda__3(x_1, x_5, x_6, x_30, x_3, x_4);
lean_dec(x_6);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_box(0);
x_7 = x_32;
goto block_17;
}
}
else
{
lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_box(0);
x_7 = x_33;
goto block_17;
}
}
else
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
x_7 = x_34;
goto block_17;
}
}
block_17:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lean_IR_Checker_checkExpr___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_Checker_checkExpr___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
lean_inc(x_3);
x_36 = l_Lean_IR_Checker_checkObjVar(x_35, x_3, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_36, 0, x_42);
return x_36;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_48);
return x_49;
}
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
lean_dec(x_2);
lean_inc(x_3);
x_52 = l_Lean_IR_Checker_checkObjVar(x_50, x_3, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_dec(x_52);
lean_inc(x_3);
x_65 = l_Lean_IR_Checker_checkArgs(x_51, x_3, x_64);
lean_dec(x_51);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_65, 0, x_71);
return x_65;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_dec(x_65);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_dec(x_65);
x_78 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_77);
return x_78;
}
}
}
case 3:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
lean_dec(x_2);
x_81 = l_Lean_IR_Checker_getType(x_80, x_3, x_4);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_81, 0, x_87);
return x_81;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_dec(x_81);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_82);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_82, 0);
switch (lean_obj_tag(x_94)) {
case 7:
{
lean_object* x_95; lean_object* x_96; 
lean_free_object(x_82);
lean_dec(x_79);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
lean_dec(x_81);
x_96 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_95);
return x_96;
}
case 8:
{
lean_object* x_97; lean_object* x_98; 
lean_free_object(x_82);
lean_dec(x_79);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_dec(x_81);
x_98 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_97);
return x_98;
}
case 9:
{
uint8_t x_99; 
lean_free_object(x_82);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_81);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_81, 0);
lean_dec(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_dec(x_94);
x_102 = lean_array_get_size(x_101);
x_103 = lean_nat_dec_lt(x_79, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_101);
lean_dec(x_79);
lean_dec(x_1);
x_104 = l_Lean_IR_Checker_checkExpr___closed__5;
lean_ctor_set(x_81, 0, x_104);
return x_81;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_array_fget(x_101, x_79);
lean_dec(x_79);
lean_dec(x_101);
x_106 = l_Lean_IR_IRType_beq(x_105, x_1);
lean_dec(x_1);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_81, 0, x_107);
return x_81;
}
else
{
lean_object* x_108; 
x_108 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_81, 0, x_108);
return x_81;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_81, 1);
lean_inc(x_109);
lean_dec(x_81);
x_110 = lean_ctor_get(x_94, 1);
lean_inc(x_110);
lean_dec(x_94);
x_111 = lean_array_get_size(x_110);
x_112 = lean_nat_dec_lt(x_79, x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec(x_79);
lean_dec(x_1);
x_113 = l_Lean_IR_Checker_checkExpr___closed__5;
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
return x_114;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_array_fget(x_110, x_79);
lean_dec(x_79);
lean_dec(x_110);
x_116 = l_Lean_IR_IRType_beq(x_115, x_1);
lean_dec(x_1);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_109);
return x_120;
}
}
}
}
case 10:
{
uint8_t x_121; 
lean_free_object(x_82);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_81);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_81, 0);
lean_dec(x_122);
x_123 = lean_ctor_get(x_94, 1);
lean_inc(x_123);
lean_dec(x_94);
x_124 = lean_array_get_size(x_123);
x_125 = lean_nat_dec_lt(x_79, x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_123);
lean_dec(x_79);
lean_dec(x_1);
x_126 = l_Lean_IR_Checker_checkExpr___closed__5;
lean_ctor_set(x_81, 0, x_126);
return x_81;
}
else
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_array_fget(x_123, x_79);
lean_dec(x_79);
lean_dec(x_123);
x_128 = l_Lean_IR_IRType_beq(x_127, x_1);
lean_dec(x_1);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_81, 0, x_129);
return x_81;
}
else
{
lean_object* x_130; 
x_130 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_81, 0, x_130);
return x_81;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_81, 1);
lean_inc(x_131);
lean_dec(x_81);
x_132 = lean_ctor_get(x_94, 1);
lean_inc(x_132);
lean_dec(x_94);
x_133 = lean_array_get_size(x_132);
x_134 = lean_nat_dec_lt(x_79, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_132);
lean_dec(x_79);
lean_dec(x_1);
x_135 = l_Lean_IR_Checker_checkExpr___closed__5;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_131);
return x_136;
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_array_fget(x_132, x_79);
lean_dec(x_79);
lean_dec(x_132);
x_138 = l_Lean_IR_IRType_beq(x_137, x_1);
lean_dec(x_1);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_131);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_131);
return x_142;
}
}
}
}
default: 
{
uint8_t x_143; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_81);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = lean_ctor_get(x_81, 0);
lean_dec(x_144);
x_145 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_94);
x_146 = l_Std_Format_defWidth;
x_147 = lean_format_pretty(x_145, x_146);
x_148 = l_Lean_IR_Checker_checkExpr___closed__3;
x_149 = lean_string_append(x_148, x_147);
lean_dec(x_147);
x_150 = l_Lean_IR_Checker_getDecl___closed__2;
x_151 = lean_string_append(x_149, x_150);
lean_ctor_set_tag(x_82, 0);
lean_ctor_set(x_82, 0, x_151);
return x_81;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_81, 1);
lean_inc(x_152);
lean_dec(x_81);
x_153 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_94);
x_154 = l_Std_Format_defWidth;
x_155 = lean_format_pretty(x_153, x_154);
x_156 = l_Lean_IR_Checker_checkExpr___closed__3;
x_157 = lean_string_append(x_156, x_155);
lean_dec(x_155);
x_158 = l_Lean_IR_Checker_getDecl___closed__2;
x_159 = lean_string_append(x_157, x_158);
lean_ctor_set_tag(x_82, 0);
lean_ctor_set(x_82, 0, x_159);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_82);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
}
}
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_82, 0);
lean_inc(x_161);
lean_dec(x_82);
switch (lean_obj_tag(x_161)) {
case 7:
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_79);
x_162 = lean_ctor_get(x_81, 1);
lean_inc(x_162);
lean_dec(x_81);
x_163 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_162);
return x_163;
}
case 8:
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_79);
x_164 = lean_ctor_get(x_81, 1);
lean_inc(x_164);
lean_dec(x_81);
x_165 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_164);
return x_165;
}
case 9:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_3);
x_166 = lean_ctor_get(x_81, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_167 = x_81;
} else {
 lean_dec_ref(x_81);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
lean_dec(x_161);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_79, x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_168);
lean_dec(x_79);
lean_dec(x_1);
x_171 = l_Lean_IR_Checker_checkExpr___closed__5;
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_array_fget(x_168, x_79);
lean_dec(x_79);
lean_dec(x_168);
x_174 = l_Lean_IR_IRType_beq(x_173, x_1);
lean_dec(x_1);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_167)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_167;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_166);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_167)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_167;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_166);
return x_178;
}
}
}
case 10:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_3);
x_179 = lean_ctor_get(x_81, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_180 = x_81;
} else {
 lean_dec_ref(x_81);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_161, 1);
lean_inc(x_181);
lean_dec(x_161);
x_182 = lean_array_get_size(x_181);
x_183 = lean_nat_dec_lt(x_79, x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_181);
lean_dec(x_79);
lean_dec(x_1);
x_184 = l_Lean_IR_Checker_checkExpr___closed__5;
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_179);
return x_185;
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_array_fget(x_181, x_79);
lean_dec(x_79);
lean_dec(x_181);
x_187 = l_Lean_IR_IRType_beq(x_186, x_1);
lean_dec(x_1);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_180)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_180;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_179);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_180)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_180;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_179);
return x_191;
}
}
}
default: 
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_1);
x_192 = lean_ctor_get(x_81, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_193 = x_81;
} else {
 lean_dec_ref(x_81);
 x_193 = lean_box(0);
}
x_194 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_161);
x_195 = l_Std_Format_defWidth;
x_196 = lean_format_pretty(x_194, x_195);
x_197 = l_Lean_IR_Checker_checkExpr___closed__3;
x_198 = lean_string_append(x_197, x_196);
lean_dec(x_196);
x_199 = l_Lean_IR_Checker_getDecl___closed__2;
x_200 = lean_string_append(x_198, x_199);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
if (lean_is_scalar(x_193)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_193;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_192);
return x_202;
}
}
}
}
}
case 4:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_2, 1);
lean_inc(x_203);
lean_dec(x_2);
lean_inc(x_3);
x_204 = l_Lean_IR_Checker_checkObjVar(x_203, x_3, x_4);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
lean_dec(x_3);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_204);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_204, 0);
lean_dec(x_207);
x_208 = !lean_is_exclusive(x_205);
if (x_208 == 0)
{
return x_204;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_205, 0);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_204, 0, x_210);
return x_204;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
x_212 = lean_ctor_get(x_205, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_213 = x_205;
} else {
 lean_dec_ref(x_205);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_211);
return x_215;
}
}
else
{
uint8_t x_216; 
lean_dec(x_205);
x_216 = !lean_is_exclusive(x_204);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_204, 1);
x_218 = lean_ctor_get(x_204, 0);
lean_dec(x_218);
x_219 = lean_box(5);
x_220 = l_Lean_IR_IRType_beq(x_1, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_free_object(x_204);
x_221 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_222 = l_Std_Format_defWidth;
x_223 = lean_format_pretty(x_221, x_222);
x_224 = l_Lean_IR_Checker_checkType___closed__1;
x_225 = lean_string_append(x_224, x_223);
lean_dec(x_223);
x_226 = l_Lean_IR_Checker_getDecl___closed__2;
x_227 = lean_string_append(x_225, x_226);
x_228 = l_Lean_IR_Checker_checkType___closed__2;
x_229 = lean_box(0);
x_230 = lean_apply_4(x_228, x_227, x_229, x_3, x_217);
return x_230;
}
else
{
lean_object* x_231; 
lean_dec(x_3);
lean_dec(x_1);
x_231 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_204, 0, x_231);
return x_204;
}
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_232 = lean_ctor_get(x_204, 1);
lean_inc(x_232);
lean_dec(x_204);
x_233 = lean_box(5);
x_234 = l_Lean_IR_IRType_beq(x_1, x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_235 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_236 = l_Std_Format_defWidth;
x_237 = lean_format_pretty(x_235, x_236);
x_238 = l_Lean_IR_Checker_checkType___closed__1;
x_239 = lean_string_append(x_238, x_237);
lean_dec(x_237);
x_240 = l_Lean_IR_Checker_getDecl___closed__2;
x_241 = lean_string_append(x_239, x_240);
x_242 = l_Lean_IR_Checker_checkType___closed__2;
x_243 = lean_box(0);
x_244 = lean_apply_4(x_242, x_241, x_243, x_3, x_232);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_3);
lean_dec(x_1);
x_245 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_232);
return x_246;
}
}
}
}
case 5:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_2, 2);
lean_inc(x_247);
lean_dec(x_2);
lean_inc(x_3);
x_248 = l_Lean_IR_Checker_checkObjVar(x_247, x_3, x_4);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
lean_dec(x_3);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_248);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_248, 0);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_249);
if (x_252 == 0)
{
return x_248;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_249, 0);
lean_inc(x_253);
lean_dec(x_249);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_248, 0, x_254);
return x_248;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_248, 1);
lean_inc(x_255);
lean_dec(x_248);
x_256 = lean_ctor_get(x_249, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_257 = x_249;
} else {
 lean_dec_ref(x_249);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_255);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_249);
x_260 = lean_ctor_get(x_248, 1);
lean_inc(x_260);
lean_dec(x_248);
x_261 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_260);
return x_261;
}
}
case 6:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_1);
x_262 = lean_ctor_get(x_2, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_2, 1);
lean_inc(x_263);
lean_dec(x_2);
x_264 = l_Lean_IR_Checker_checkFullApp(x_262, x_263, x_3, x_4);
lean_dec(x_263);
return x_264;
}
case 7:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_2, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_2, 1);
lean_inc(x_266);
lean_dec(x_2);
lean_inc(x_3);
x_267 = l_Lean_IR_Checker_checkPartialApp(x_265, x_266, x_3, x_4);
lean_dec(x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
lean_dec(x_3);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_267);
if (x_269 == 0)
{
lean_object* x_270; uint8_t x_271; 
x_270 = lean_ctor_get(x_267, 0);
lean_dec(x_270);
x_271 = !lean_is_exclusive(x_268);
if (x_271 == 0)
{
return x_267;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_268, 0);
lean_inc(x_272);
lean_dec(x_268);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_267, 0, x_273);
return x_267;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_267, 1);
lean_inc(x_274);
lean_dec(x_267);
x_275 = lean_ctor_get(x_268, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_276 = x_268;
} else {
 lean_dec_ref(x_268);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_274);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_268);
x_279 = lean_ctor_get(x_267, 1);
lean_inc(x_279);
lean_dec(x_267);
x_280 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_279);
return x_280;
}
}
case 8:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_1);
x_281 = lean_ctor_get(x_2, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_2, 1);
lean_inc(x_282);
lean_dec(x_2);
lean_inc(x_3);
x_283 = l_Lean_IR_Checker_checkObjVar(x_281, x_3, x_4);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
lean_dec(x_282);
lean_dec(x_3);
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
lean_object* x_295; lean_object* x_296; 
lean_dec(x_284);
x_295 = lean_ctor_get(x_283, 1);
lean_inc(x_295);
lean_dec(x_283);
x_296 = l_Lean_IR_Checker_checkArgs(x_282, x_3, x_295);
lean_dec(x_282);
return x_296;
}
}
case 9:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_2, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_2, 1);
lean_inc(x_298);
lean_dec(x_2);
lean_inc(x_3);
x_299 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
uint8_t x_301; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_3);
x_301 = !lean_is_exclusive(x_299);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_299, 0);
lean_dec(x_302);
x_303 = !lean_is_exclusive(x_300);
if (x_303 == 0)
{
return x_299;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_300, 0);
lean_inc(x_304);
lean_dec(x_300);
x_305 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_299, 0, x_305);
return x_299;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_299, 1);
lean_inc(x_306);
lean_dec(x_299);
x_307 = lean_ctor_get(x_300, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_308 = x_300;
} else {
 lean_dec_ref(x_300);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(0, 1, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_307);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_306);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_300);
x_311 = lean_ctor_get(x_299, 1);
lean_inc(x_311);
lean_dec(x_299);
lean_inc(x_3);
lean_inc(x_298);
x_312 = l_Lean_IR_Checker_checkScalarVar(x_298, x_3, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_3);
x_314 = !lean_is_exclusive(x_312);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_312, 0);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_313);
if (x_316 == 0)
{
return x_312;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_313, 0);
lean_inc(x_317);
lean_dec(x_313);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_312, 0, x_318);
return x_312;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_312, 1);
lean_inc(x_319);
lean_dec(x_312);
x_320 = lean_ctor_get(x_313, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_321 = x_313;
} else {
 lean_dec_ref(x_313);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(0, 1, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_320);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_319);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_313);
x_324 = lean_ctor_get(x_312, 1);
lean_inc(x_324);
lean_dec(x_312);
x_325 = l_Lean_IR_Checker_getType(x_298, x_3, x_324);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
uint8_t x_327; 
lean_dec(x_297);
lean_dec(x_3);
x_327 = !lean_is_exclusive(x_325);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_ctor_get(x_325, 0);
lean_dec(x_328);
x_329 = !lean_is_exclusive(x_326);
if (x_329 == 0)
{
return x_325;
}
else
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_326, 0);
lean_inc(x_330);
lean_dec(x_326);
x_331 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_325, 0, x_331);
return x_325;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_325, 1);
lean_inc(x_332);
lean_dec(x_325);
x_333 = lean_ctor_get(x_326, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_334 = x_326;
} else {
 lean_dec_ref(x_326);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(0, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_333);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_332);
return x_336;
}
}
else
{
uint8_t x_337; 
x_337 = !lean_is_exclusive(x_325);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_338 = lean_ctor_get(x_325, 1);
x_339 = lean_ctor_get(x_325, 0);
lean_dec(x_339);
x_340 = lean_ctor_get(x_326, 0);
lean_inc(x_340);
lean_dec(x_326);
x_341 = l_Lean_IR_IRType_beq(x_340, x_297);
lean_dec(x_297);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_free_object(x_325);
x_342 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_340);
x_343 = l_Std_Format_defWidth;
x_344 = lean_format_pretty(x_342, x_343);
x_345 = l_Lean_IR_Checker_checkType___closed__1;
x_346 = lean_string_append(x_345, x_344);
lean_dec(x_344);
x_347 = l_Lean_IR_Checker_getDecl___closed__2;
x_348 = lean_string_append(x_346, x_347);
x_349 = l_Lean_IR_Checker_checkType___closed__2;
x_350 = lean_box(0);
x_351 = lean_apply_4(x_349, x_348, x_350, x_3, x_338);
return x_351;
}
else
{
lean_object* x_352; 
lean_dec(x_340);
lean_dec(x_3);
x_352 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_325, 0, x_352);
return x_325;
}
}
else
{
lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_353 = lean_ctor_get(x_325, 1);
lean_inc(x_353);
lean_dec(x_325);
x_354 = lean_ctor_get(x_326, 0);
lean_inc(x_354);
lean_dec(x_326);
x_355 = l_Lean_IR_IRType_beq(x_354, x_297);
lean_dec(x_297);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_356 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_354);
x_357 = l_Std_Format_defWidth;
x_358 = lean_format_pretty(x_356, x_357);
x_359 = l_Lean_IR_Checker_checkType___closed__1;
x_360 = lean_string_append(x_359, x_358);
lean_dec(x_358);
x_361 = l_Lean_IR_Checker_getDecl___closed__2;
x_362 = lean_string_append(x_360, x_361);
x_363 = l_Lean_IR_Checker_checkType___closed__2;
x_364 = lean_box(0);
x_365 = lean_apply_4(x_363, x_362, x_364, x_3, x_353);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_354);
lean_dec(x_3);
x_366 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_353);
return x_367;
}
}
}
}
}
}
case 10:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_2, 0);
lean_inc(x_368);
lean_dec(x_2);
lean_inc(x_3);
x_369 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
uint8_t x_371; 
lean_dec(x_368);
lean_dec(x_3);
x_371 = !lean_is_exclusive(x_369);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; 
x_372 = lean_ctor_get(x_369, 0);
lean_dec(x_372);
x_373 = !lean_is_exclusive(x_370);
if (x_373 == 0)
{
return x_369;
}
else
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_370, 0);
lean_inc(x_374);
lean_dec(x_370);
x_375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_369, 0, x_375);
return x_369;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_ctor_get(x_369, 1);
lean_inc(x_376);
lean_dec(x_369);
x_377 = lean_ctor_get(x_370, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 x_378 = x_370;
} else {
 lean_dec_ref(x_370);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_376);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; 
lean_dec(x_370);
x_381 = lean_ctor_get(x_369, 1);
lean_inc(x_381);
lean_dec(x_369);
x_382 = l_Lean_IR_Checker_checkObjVar(x_368, x_3, x_381);
return x_382;
}
}
case 11:
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_2, 0);
lean_inc(x_383);
lean_dec(x_2);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_383);
lean_dec(x_3);
lean_dec(x_1);
x_384 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_4);
return x_385;
}
else
{
lean_object* x_386; 
lean_dec(x_383);
x_386 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
return x_386;
}
}
default: 
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_2, 0);
lean_inc(x_387);
lean_dec(x_2);
lean_inc(x_3);
x_388 = l_Lean_IR_Checker_checkObjVar(x_387, x_3, x_4);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
uint8_t x_390; 
lean_dec(x_3);
lean_dec(x_1);
x_390 = !lean_is_exclusive(x_388);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_388, 0);
lean_dec(x_391);
x_392 = !lean_is_exclusive(x_389);
if (x_392 == 0)
{
return x_388;
}
else
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_389, 0);
lean_inc(x_393);
lean_dec(x_389);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_388, 0, x_394);
return x_388;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_395 = lean_ctor_get(x_388, 1);
lean_inc(x_395);
lean_dec(x_388);
x_396 = lean_ctor_get(x_389, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_397 = x_389;
} else {
 lean_dec_ref(x_389);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(0, 1, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_396);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_395);
return x_399;
}
}
else
{
uint8_t x_400; 
lean_dec(x_389);
x_400 = !lean_is_exclusive(x_388);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_401 = lean_ctor_get(x_388, 1);
x_402 = lean_ctor_get(x_388, 0);
lean_dec(x_402);
x_403 = lean_box(1);
x_404 = l_Lean_IR_IRType_beq(x_1, x_403);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_free_object(x_388);
x_405 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_406 = l_Std_Format_defWidth;
x_407 = lean_format_pretty(x_405, x_406);
x_408 = l_Lean_IR_Checker_checkType___closed__1;
x_409 = lean_string_append(x_408, x_407);
lean_dec(x_407);
x_410 = l_Lean_IR_Checker_getDecl___closed__2;
x_411 = lean_string_append(x_409, x_410);
x_412 = l_Lean_IR_Checker_checkType___closed__2;
x_413 = lean_box(0);
x_414 = lean_apply_4(x_412, x_411, x_413, x_3, x_401);
return x_414;
}
else
{
lean_object* x_415; 
lean_dec(x_3);
lean_dec(x_1);
x_415 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_388, 0, x_415);
return x_388;
}
}
else
{
lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_416 = lean_ctor_get(x_388, 1);
lean_inc(x_416);
lean_dec(x_388);
x_417 = lean_box(1);
x_418 = l_Lean_IR_IRType_beq(x_1, x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_419 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_420 = l_Std_Format_defWidth;
x_421 = lean_format_pretty(x_419, x_420);
x_422 = l_Lean_IR_Checker_checkType___closed__1;
x_423 = lean_string_append(x_422, x_421);
lean_dec(x_421);
x_424 = l_Lean_IR_Checker_getDecl___closed__2;
x_425 = lean_string_append(x_423, x_424);
x_426 = l_Lean_IR_Checker_checkType___closed__2;
x_427 = lean_box(0);
x_428 = lean_apply_4(x_426, x_425, x_427, x_3, x_416);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_3);
lean_dec(x_1);
x_429 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_416);
return x_430;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkExpr___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkExpr___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkExpr___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_inc(x_5);
x_10 = l_Lean_IR_Checker_markIndex(x_9, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_11);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_IR_LocalContext_addParam(x_4, x_8);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_23;
x_6 = x_22;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = lean_apply_2(x_2, x_3, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_apply_2(x_2, x_16, x_4);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_8, x_8);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_apply_2(x_2, x_3, x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
x_25 = lean_apply_2(x_2, x_24, x_4);
return x_25;
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(x_1, x_26, x_27, x_6, x_3, x_4);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_3, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_28, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_28, 0, x_38);
return x_28;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
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
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
lean_ctor_set(x_3, 1, x_45);
x_46 = lean_apply_2(x_2, x_3, x_44);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_3);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_49 = x_28;
} else {
 lean_dec_ref(x_28);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_dec(x_28);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_7);
x_57 = lean_apply_2(x_2, x_56, x_54);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_withParams(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
lean_inc(x_5);
x_10 = l_Lean_IR_Checker_checkFnBody(x_9, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
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
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_23;
x_6 = x_22;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_5);
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
lean_inc(x_2);
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
lean_inc(x_2);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_49);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_61 = x_48;
} else {
 lean_dec_ref(x_48);
 x_61 = lean_box(0);
}
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 2);
lean_inc(x_82);
x_83 = lean_array_get_size(x_45);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_81);
lean_ctor_set(x_86, 2, x_82);
lean_inc(x_46);
x_87 = l_Lean_IR_Checker_checkFnBody(x_46, x_86, x_60);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_62 = x_88;
x_63 = x_89;
goto block_79;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_83, x_83);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_83);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_82);
lean_inc(x_46);
x_92 = l_Lean_IR_Checker_checkFnBody(x_46, x_91, x_60);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_62 = x_93;
x_63 = x_94;
goto block_79;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
x_95 = 0;
x_96 = lean_usize_of_nat(x_83);
lean_dec(x_83);
lean_inc(x_2);
x_97 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(x_45, x_95, x_96, x_81, x_2, x_60);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_82);
lean_dec(x_80);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
x_62 = x_98;
x_63 = x_99;
goto block_79;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_62 = x_102;
x_63 = x_99;
goto block_79;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
lean_dec(x_97);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_80);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_82);
lean_inc(x_46);
x_106 = l_Lean_IR_Checker_checkFnBody(x_46, x_105, x_103);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_62 = x_107;
x_63 = x_108;
goto block_79;
}
}
}
block_79:
{
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_64; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_62);
lean_dec(x_61);
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_2, 1);
x_71 = l_Lean_IR_LocalContext_addJP(x_70, x_44, x_45, x_46);
lean_ctor_set(x_2, 1, x_71);
x_1 = x_47;
x_3 = x_63;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
x_76 = l_Lean_IR_LocalContext_addJP(x_74, x_44, x_45, x_46);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
x_1 = x_47;
x_2 = x_77;
x_3 = x_63;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 3);
lean_inc(x_111);
lean_dec(x_1);
x_112 = l_Lean_IR_Checker_checkVar(x_109, x_2, x_3);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_2);
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
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_113);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
lean_dec(x_112);
x_125 = l_Lean_IR_Checker_checkArg(x_110, x_2, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_111);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_125, 0);
lean_dec(x_128);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_125, 0, x_131);
return x_125;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_125, 1);
lean_inc(x_132);
lean_dec(x_125);
x_133 = lean_ctor_get(x_126, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_134 = x_126;
} else {
 lean_dec_ref(x_126);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 1, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
}
else
{
lean_object* x_137; 
lean_dec(x_126);
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
lean_dec(x_125);
x_1 = x_111;
x_3 = x_137;
goto _start;
}
}
}
case 4:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 3);
lean_inc(x_141);
lean_dec(x_1);
x_142 = l_Lean_IR_Checker_checkVar(x_139, x_2, x_3);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_142);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_142, 0);
lean_dec(x_145);
x_146 = !lean_is_exclusive(x_143);
if (x_146 == 0)
{
return x_142;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_142, 0, x_148);
return x_142;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
lean_dec(x_142);
x_150 = lean_ctor_get(x_143, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_151 = x_143;
} else {
 lean_dec_ref(x_143);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_149);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_143);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
lean_dec(x_142);
x_155 = l_Lean_IR_Checker_checkVar(x_140, x_2, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
lean_dec(x_141);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_155);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_155, 0);
lean_dec(x_158);
x_159 = !lean_is_exclusive(x_156);
if (x_159 == 0)
{
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_155, 0, x_161);
return x_155;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_163 = lean_ctor_get(x_156, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_164 = x_156;
} else {
 lean_dec_ref(x_156);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_162);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_156);
x_167 = lean_ctor_get(x_155, 1);
lean_inc(x_167);
lean_dec(x_155);
x_1 = x_141;
x_3 = x_167;
goto _start;
}
}
}
case 5:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_1, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_1, 5);
lean_inc(x_171);
lean_dec(x_1);
x_172 = l_Lean_IR_Checker_checkVar(x_169, x_2, x_3);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_172);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_173);
if (x_176 == 0)
{
return x_172;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_172, 0, x_178);
return x_172;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_dec(x_172);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_181 = x_173;
} else {
 lean_dec_ref(x_173);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_173);
x_184 = lean_ctor_get(x_172, 1);
lean_inc(x_184);
lean_dec(x_172);
x_185 = l_Lean_IR_Checker_checkVar(x_170, x_2, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
lean_dec(x_171);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_185);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_185, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
return x_185;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
lean_dec(x_186);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_185, 0, x_191);
return x_185;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_185, 1);
lean_inc(x_192);
lean_dec(x_185);
x_193 = lean_ctor_get(x_186, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
return x_196;
}
}
else
{
lean_object* x_197; 
lean_dec(x_186);
x_197 = lean_ctor_get(x_185, 1);
lean_inc(x_197);
lean_dec(x_185);
x_1 = x_171;
x_3 = x_197;
goto _start;
}
}
}
case 8:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_1, 1);
lean_inc(x_200);
lean_dec(x_1);
x_201 = l_Lean_IR_Checker_checkVar(x_199, x_2, x_3);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
lean_dec(x_200);
lean_dec(x_2);
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
lean_object* x_213; 
lean_dec(x_202);
x_213 = lean_ctor_get(x_201, 1);
lean_inc(x_213);
lean_dec(x_201);
x_1 = x_200;
x_3 = x_213;
goto _start;
}
}
case 9:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_1, 1);
lean_inc(x_215);
lean_dec(x_1);
x_1 = x_215;
goto _start;
}
case 10:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_1, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_1, 3);
lean_inc(x_218);
lean_dec(x_1);
x_219 = l_Lean_IR_Checker_checkVar(x_217, x_2, x_3);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
lean_dec(x_218);
lean_dec(x_2);
x_221 = !lean_is_exclusive(x_219);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_219, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_220);
if (x_223 == 0)
{
return x_219;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
lean_dec(x_220);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_219, 0, x_225);
return x_219;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
lean_dec(x_219);
x_227 = lean_ctor_get(x_220, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_228 = x_220;
} else {
 lean_dec_ref(x_220);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_226);
return x_230;
}
}
else
{
uint8_t x_231; 
lean_dec(x_220);
x_231 = !lean_is_exclusive(x_219);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_232 = lean_ctor_get(x_219, 1);
x_233 = lean_ctor_get(x_219, 0);
lean_dec(x_233);
x_234 = lean_array_get_size(x_218);
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_nat_dec_lt(x_235, x_234);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_234);
lean_dec(x_218);
lean_dec(x_2);
x_237 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_219, 0, x_237);
return x_219;
}
else
{
uint8_t x_238; 
x_238 = lean_nat_dec_le(x_234, x_234);
if (x_238 == 0)
{
lean_object* x_239; 
lean_dec(x_234);
lean_dec(x_218);
lean_dec(x_2);
x_239 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_219, 0, x_239);
return x_219;
}
else
{
size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; 
lean_free_object(x_219);
x_240 = 0;
x_241 = lean_usize_of_nat(x_234);
lean_dec(x_234);
x_242 = lean_box(0);
x_243 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(x_218, x_240, x_241, x_242, x_2, x_232);
lean_dec(x_218);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = lean_ctor_get(x_219, 1);
lean_inc(x_244);
lean_dec(x_219);
x_245 = lean_array_get_size(x_218);
x_246 = lean_unsigned_to_nat(0u);
x_247 = lean_nat_dec_lt(x_246, x_245);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_245);
lean_dec(x_218);
lean_dec(x_2);
x_248 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_244);
return x_249;
}
else
{
uint8_t x_250; 
x_250 = lean_nat_dec_le(x_245, x_245);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_245);
lean_dec(x_218);
lean_dec(x_2);
x_251 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_244);
return x_252;
}
else
{
size_t x_253; size_t x_254; lean_object* x_255; lean_object* x_256; 
x_253 = 0;
x_254 = lean_usize_of_nat(x_245);
lean_dec(x_245);
x_255 = lean_box(0);
x_256 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(x_218, x_253, x_254, x_255, x_2, x_244);
lean_dec(x_218);
return x_256;
}
}
}
}
}
case 11:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_1, 0);
lean_inc(x_257);
lean_dec(x_1);
x_258 = l_Lean_IR_Checker_checkArg(x_257, x_2, x_3);
lean_dec(x_2);
return x_258;
}
case 12:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_1, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_1, 1);
lean_inc(x_260);
lean_dec(x_1);
x_261 = l_Lean_IR_Checker_checkJP(x_259, x_2, x_3);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
lean_dec(x_260);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_261);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_261, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_262);
if (x_265 == 0)
{
return x_261;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_262, 0);
lean_inc(x_266);
lean_dec(x_262);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_261, 0, x_267);
return x_261;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_261, 1);
lean_inc(x_268);
lean_dec(x_261);
x_269 = lean_ctor_get(x_262, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_270 = x_262;
} else {
 lean_dec_ref(x_262);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(0, 1, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_268);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_262);
x_273 = lean_ctor_get(x_261, 1);
lean_inc(x_273);
lean_dec(x_261);
x_274 = l_Lean_IR_Checker_checkArgs(x_260, x_2, x_273);
lean_dec(x_260);
return x_274;
}
}
case 13:
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_2);
x_275 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_3);
return x_276;
}
default: 
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_1, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_1, 2);
lean_inc(x_278);
lean_dec(x_1);
x_279 = l_Lean_IR_Checker_checkVar(x_277, x_2, x_3);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
if (lean_obj_tag(x_280) == 0)
{
uint8_t x_281; 
lean_dec(x_278);
lean_dec(x_2);
x_281 = !lean_is_exclusive(x_279);
if (x_281 == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_279, 0);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_280);
if (x_283 == 0)
{
return x_279;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_280, 0);
lean_inc(x_284);
lean_dec(x_280);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_279, 0, x_285);
return x_279;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_279, 1);
lean_inc(x_286);
lean_dec(x_279);
x_287 = lean_ctor_get(x_280, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_288 = x_280;
} else {
 lean_dec_ref(x_280);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_286);
return x_290;
}
}
else
{
lean_object* x_291; 
lean_dec(x_280);
x_291 = lean_ctor_get(x_279, 1);
lean_inc(x_291);
lean_dec(x_279);
x_1 = x_278;
x_3 = x_291;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_array_get_size(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = l_Lean_IR_Checker_checkFnBody(x_5, x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 2, x_8);
x_18 = l_Lean_IR_Checker_checkFnBody(x_5, x_17, x_3);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_9, x_9);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = l_Lean_IR_Checker_checkFnBody(x_5, x_2, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_8);
x_26 = l_Lean_IR_Checker_checkFnBody(x_5, x_25, x_3);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_9);
lean_dec(x_9);
lean_inc(x_2);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(x_4, x_27, x_28, x_7, x_2, x_3);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_2, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_2, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_29, 0, x_39);
return x_29;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
lean_ctor_set(x_2, 1, x_46);
x_47 = l_Lean_IR_Checker_checkFnBody(x_5, x_2, x_45);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_50 = x_29;
} else {
 lean_dec_ref(x_29);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_6);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_8);
x_58 = l_Lean_IR_Checker_checkFnBody(x_5, x_57, x_55);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
x_61 = lean_array_get_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_64 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_61, x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_67 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(x_59, x_69, x_70, x_60, x_2, x_3);
lean_dec(x_59);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_71, 0, x_77);
return x_71;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_72);
x_83 = !lean_is_exclusive(x_71);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_71, 0);
lean_dec(x_84);
x_85 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_71, 0, x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiler IR check failed at '", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', error: ", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_13, x_14);
x_16 = l_Lean_IR_checkDecl___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_checkDecl___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_12);
lean_dec(x_12);
x_21 = l_Lean_IR_Checker_checkType___closed__3;
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
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_31, x_32);
x_34 = l_Lean_IR_checkDecl___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_IR_checkDecl___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_30);
lean_dec(x_30);
x_39 = l_Lean_IR_Checker_checkType___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = l_Lean_IR_checkDecl(x_1, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_12, x_13, x_14, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Checker_maxCtorFields___closed__1 = _init_l_Lean_IR_Checker_maxCtorFields___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields___closed__1);
l_Lean_IR_Checker_maxCtorFields = _init_l_Lean_IR_Checker_maxCtorFields();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields);
l_Lean_IR_Checker_maxCtorScalarsSize___closed__1 = _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize___closed__1);
l_Lean_IR_Checker_maxCtorScalarsSize = _init_l_Lean_IR_Checker_maxCtorScalarsSize();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize);
l_Lean_IR_Checker_maxCtorTag___closed__1 = _init_l_Lean_IR_Checker_maxCtorTag___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag___closed__1);
l_Lean_IR_Checker_maxCtorTag = _init_l_Lean_IR_Checker_maxCtorTag();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag);
l_Lean_IR_Checker_usizeSize___closed__1 = _init_l_Lean_IR_Checker_usizeSize___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_usizeSize___closed__1);
l_Lean_IR_Checker_usizeSize = _init_l_Lean_IR_Checker_usizeSize();
lean_mark_persistent(l_Lean_IR_Checker_usizeSize);
l_Lean_IR_Checker_CheckerContext_localCtx___default = _init_l_Lean_IR_Checker_CheckerContext_localCtx___default();
lean_mark_persistent(l_Lean_IR_Checker_CheckerContext_localCtx___default);
l_Lean_IR_Checker_CheckerState_foundVars___default = _init_l_Lean_IR_Checker_CheckerState_foundVars___default();
lean_mark_persistent(l_Lean_IR_Checker_CheckerState_foundVars___default);
l_Lean_IR_Checker_markIndex___lambda__1___closed__1 = _init_l_Lean_IR_Checker_markIndex___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___lambda__1___closed__1);
l_Lean_IR_Checker_markIndex___closed__1 = _init_l_Lean_IR_Checker_markIndex___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__1);
l_Lean_IR_Checker_markIndex___closed__2 = _init_l_Lean_IR_Checker_markIndex___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__2);
l_Lean_IR_Checker_getDecl___closed__1 = _init_l_Lean_IR_Checker_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__1);
l_Lean_IR_Checker_getDecl___closed__2 = _init_l_Lean_IR_Checker_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__2);
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
l_Lean_IR_Checker_checkJP___closed__2 = _init_l_Lean_IR_Checker_checkJP___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__2);
l_Lean_IR_Checker_checkEqTypes___closed__1 = _init_l_Lean_IR_Checker_checkEqTypes___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__1);
l_Lean_IR_Checker_checkEqTypes___closed__2 = _init_l_Lean_IR_Checker_checkEqTypes___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__2);
l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
l_Lean_IR_Checker_checkType___closed__2 = _init_l_Lean_IR_Checker_checkType___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__2);
l_Lean_IR_Checker_checkType___closed__3 = _init_l_Lean_IR_Checker_checkType___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__3);
l_Lean_IR_Checker_checkType___closed__4 = _init_l_Lean_IR_Checker_checkType___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__4);
l_Lean_IR_Checker_checkObjType___closed__1 = _init_l_Lean_IR_Checker_checkObjType___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkObjType___closed__1);
l_Lean_IR_Checker_checkScalarType___closed__1 = _init_l_Lean_IR_Checker_checkScalarType___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkScalarType___closed__1);
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
l_Lean_IR_Checker_checkExpr___lambda__2___closed__1 = _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___lambda__2___closed__1);
l_Lean_IR_Checker_checkExpr___lambda__2___closed__2 = _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___lambda__2___closed__2);
l_Lean_IR_Checker_checkExpr___lambda__3___closed__1 = _init_l_Lean_IR_Checker_checkExpr___lambda__3___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___lambda__3___closed__1);
l_Lean_IR_Checker_checkExpr___closed__1 = _init_l_Lean_IR_Checker_checkExpr___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__1);
l_Lean_IR_Checker_checkExpr___closed__2 = _init_l_Lean_IR_Checker_checkExpr___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__2);
l_Lean_IR_Checker_checkExpr___closed__3 = _init_l_Lean_IR_Checker_checkExpr___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__3);
l_Lean_IR_Checker_checkExpr___closed__4 = _init_l_Lean_IR_Checker_checkExpr___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__4);
l_Lean_IR_Checker_checkExpr___closed__5 = _init_l_Lean_IR_Checker_checkExpr___closed__5();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__5);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__1);
l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
