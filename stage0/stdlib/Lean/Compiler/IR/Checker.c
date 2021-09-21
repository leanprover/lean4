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
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__4;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_usizeSize___closed__1;
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__1;
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerContext_localCtx___default;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorScalarsSize___closed__1;
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_IR_Checker_getDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__1;
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__1;
static lean_object* l_Lean_IR_Checker_checkVar___closed__2;
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__2;
static lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___closed__2;
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_checkDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerState_foundVars___default;
static lean_object* l_Lean_IR_Checker_checkType___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_checkDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___closed__2;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
static lean_object* l_Lean_IR_Checker_markIndex___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize(lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields(lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__2;
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
lean_object* l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(LEAN_MAX_CTOR_FIELDS);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_box(LEAN_MAX_CTOR_FIELDS);
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
x_2 = lean_box(LEAN_MAX_CTOR_SCALARS_SIZE);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_box(LEAN_MAX_CTOR_SCALARS_SIZE);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(sizeof(size_t));
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_box(sizeof(size_t));
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
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_1, x_5);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(x_3, x_1);
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
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at_Lean_IR_Checker_markIndex___spec__1(x_1, x_2);
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
x_1 = lean_mk_string("unknown declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_mk_string("x_");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown variable '");
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
x_1 = lean_mk_string("block_");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkJP___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown join point '");
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
x_7 = x_2 == x_3;
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
x_24 = x_2 + x_23;
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
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type '");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Std_Format_defWidth;
x_9 = lean_format_pretty(x_7, x_8);
x_10 = l_Lean_IR_Checker_checkType___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_16 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isObj(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = l_Std_Format_defWidth;
x_7 = lean_format_pretty(x_5, x_6);
x_8 = l_Lean_IR_Checker_checkType___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_getDecl___closed__2;
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
lean_dec(x_1);
x_14 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isScalar(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = l_Std_Format_defWidth;
x_7 = lean_format_pretty(x_5, x_6);
x_8 = l_Lean_IR_Checker_checkType___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_getDecl___closed__2;
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
lean_dec(x_1);
x_14 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_24 = l_Std_Format_defWidth;
x_25 = lean_format_pretty(x_23, x_24);
x_26 = l_Lean_IR_Checker_checkType___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_30 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_35 = l_Std_Format_defWidth;
x_36 = lean_format_pretty(x_34, x_35);
x_37 = l_Lean_IR_Checker_checkType___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_42 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_49 = l_Std_Format_defWidth;
x_50 = lean_format_pretty(x_48, x_49);
x_51 = l_Lean_IR_Checker_checkType___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_57 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
x_22 = l_Std_Format_defWidth;
x_23 = lean_format_pretty(x_21, x_22);
x_24 = l_Lean_IR_Checker_checkType___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_28 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_32 = l_Std_Format_defWidth;
x_33 = lean_format_pretty(x_31, x_32);
x_34 = l_Lean_IR_Checker_checkType___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_39 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_45 = l_Std_Format_defWidth;
x_46 = lean_format_pretty(x_44, x_45);
x_47 = l_Lean_IR_Checker_checkType___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_53 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
x_22 = l_Std_Format_defWidth;
x_23 = lean_format_pretty(x_21, x_22);
x_24 = l_Lean_IR_Checker_checkType___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_28 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_32 = l_Std_Format_defWidth;
x_33 = lean_format_pretty(x_31, x_32);
x_34 = l_Lean_IR_Checker_checkType___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_39 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
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
x_45 = l_Std_Format_defWidth;
x_46 = lean_format_pretty(x_44, x_45);
x_47 = l_Lean_IR_Checker_checkType___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_IR_Checker_getDecl___closed__2;
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
x_53 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
x_1 = lean_mk_string("incorrect number of arguments to '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', ");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" provided, ");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_38 = l_Lean_IR_Checker_checkPartialApp___closed__4;
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
x_58 = l_Lean_IR_Checker_checkPartialApp___closed__4;
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
x_81 = l_Lean_IR_Checker_checkPartialApp___closed__4;
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
x_1 = lean_mk_string("constructor '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has too many scalar fields");
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
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has too many fields");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected IR type '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid proj index");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkExpr___closed__3;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = l_Lean_IR_Checker_maxCtorFields;
x_9 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_IR_Checker_checkExpr___lambda__2(x_1, x_5, x_6, x_10, x_3, x_4);
lean_dec(x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_12, x_13);
x_15 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_IR_Checker_checkExpr___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lean_IR_Checker_checkObjVar(x_21, x_3, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_34);
lean_dec(x_3);
return x_35;
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
lean_dec(x_2);
x_38 = l_Lean_IR_Checker_checkObjVar(x_36, x_3, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_38, 0, x_44);
return x_38;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
lean_inc(x_3);
x_51 = l_Lean_IR_Checker_checkArgs(x_37, x_3, x_50);
lean_dec(x_37);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_51, 0, x_57);
return x_51;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_52);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_64 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_63);
lean_dec(x_3);
return x_64;
}
}
}
case 3:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
lean_dec(x_2);
x_67 = l_Lean_IR_Checker_getType(x_66, x_3, x_4);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_65);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_67, 0, x_73);
return x_67;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_dec(x_67);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_68);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_68, 0);
switch (lean_obj_tag(x_80)) {
case 7:
{
lean_object* x_81; lean_object* x_82; 
lean_free_object(x_68);
lean_dec(x_65);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
lean_dec(x_67);
x_82 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_81);
lean_dec(x_3);
return x_82;
}
case 8:
{
lean_object* x_83; lean_object* x_84; 
lean_free_object(x_68);
lean_dec(x_65);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_dec(x_67);
x_84 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_83);
lean_dec(x_3);
return x_84;
}
case 9:
{
uint8_t x_85; 
lean_free_object(x_68);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_67);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_67, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_dec(x_80);
x_88 = lean_array_get_size(x_87);
x_89 = lean_nat_dec_lt(x_65, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_65);
lean_dec(x_1);
x_90 = l_Lean_IR_Checker_checkExpr___closed__4;
lean_ctor_set(x_67, 0, x_90);
return x_67;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_array_fget(x_87, x_65);
lean_dec(x_65);
lean_dec(x_87);
x_92 = l_Lean_IR_IRType_beq(x_91, x_1);
lean_dec(x_1);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_67, 0, x_93);
return x_67;
}
else
{
lean_object* x_94; 
x_94 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_67, 0, x_94);
return x_67;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_67, 1);
lean_inc(x_95);
lean_dec(x_67);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
lean_dec(x_80);
x_97 = lean_array_get_size(x_96);
x_98 = lean_nat_dec_lt(x_65, x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec(x_65);
lean_dec(x_1);
x_99 = l_Lean_IR_Checker_checkExpr___closed__4;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_array_fget(x_96, x_65);
lean_dec(x_65);
lean_dec(x_96);
x_102 = l_Lean_IR_IRType_beq(x_101, x_1);
lean_dec(x_1);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_95);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_95);
return x_106;
}
}
}
}
case 10:
{
uint8_t x_107; 
lean_free_object(x_68);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_67);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_67, 0);
lean_dec(x_108);
x_109 = lean_ctor_get(x_80, 1);
lean_inc(x_109);
lean_dec(x_80);
x_110 = lean_array_get_size(x_109);
x_111 = lean_nat_dec_lt(x_65, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_65);
lean_dec(x_1);
x_112 = l_Lean_IR_Checker_checkExpr___closed__4;
lean_ctor_set(x_67, 0, x_112);
return x_67;
}
else
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_array_fget(x_109, x_65);
lean_dec(x_65);
lean_dec(x_109);
x_114 = l_Lean_IR_IRType_beq(x_113, x_1);
lean_dec(x_1);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_67, 0, x_115);
return x_67;
}
else
{
lean_object* x_116; 
x_116 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_67, 0, x_116);
return x_67;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_67, 1);
lean_inc(x_117);
lean_dec(x_67);
x_118 = lean_ctor_get(x_80, 1);
lean_inc(x_118);
lean_dec(x_80);
x_119 = lean_array_get_size(x_118);
x_120 = lean_nat_dec_lt(x_65, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_118);
lean_dec(x_65);
lean_dec(x_1);
x_121 = l_Lean_IR_Checker_checkExpr___closed__4;
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_array_fget(x_118, x_65);
lean_dec(x_65);
lean_dec(x_118);
x_124 = l_Lean_IR_IRType_beq(x_123, x_1);
lean_dec(x_1);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_117);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_117);
return x_128;
}
}
}
}
default: 
{
uint8_t x_129; 
lean_dec(x_65);
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_67);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_130 = lean_ctor_get(x_67, 0);
lean_dec(x_130);
x_131 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_80);
x_132 = l_Std_Format_defWidth;
x_133 = lean_format_pretty(x_131, x_132);
x_134 = l_Lean_IR_Checker_checkExpr___closed__2;
x_135 = lean_string_append(x_134, x_133);
lean_dec(x_133);
x_136 = l_Lean_IR_Checker_getDecl___closed__2;
x_137 = lean_string_append(x_135, x_136);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_137);
return x_67;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_ctor_get(x_67, 1);
lean_inc(x_138);
lean_dec(x_67);
x_139 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_80);
x_140 = l_Std_Format_defWidth;
x_141 = lean_format_pretty(x_139, x_140);
x_142 = l_Lean_IR_Checker_checkExpr___closed__2;
x_143 = lean_string_append(x_142, x_141);
lean_dec(x_141);
x_144 = l_Lean_IR_Checker_getDecl___closed__2;
x_145 = lean_string_append(x_143, x_144);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_145);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_68);
lean_ctor_set(x_146, 1, x_138);
return x_146;
}
}
}
}
else
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_68, 0);
lean_inc(x_147);
lean_dec(x_68);
switch (lean_obj_tag(x_147)) {
case 7:
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_65);
x_148 = lean_ctor_get(x_67, 1);
lean_inc(x_148);
lean_dec(x_67);
x_149 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_148);
lean_dec(x_3);
return x_149;
}
case 8:
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_65);
x_150 = lean_ctor_get(x_67, 1);
lean_inc(x_150);
lean_dec(x_67);
x_151 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_150);
lean_dec(x_3);
return x_151;
}
case 9:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_3);
x_152 = lean_ctor_get(x_67, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_153 = x_67;
} else {
 lean_dec_ref(x_67);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_dec(x_147);
x_155 = lean_array_get_size(x_154);
x_156 = lean_nat_dec_lt(x_65, x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
lean_dec(x_65);
lean_dec(x_1);
x_157 = l_Lean_IR_Checker_checkExpr___closed__4;
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_152);
return x_158;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_array_fget(x_154, x_65);
lean_dec(x_65);
lean_dec(x_154);
x_160 = l_Lean_IR_IRType_beq(x_159, x_1);
lean_dec(x_1);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_153;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_152);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_153)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_153;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_152);
return x_164;
}
}
}
case 10:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_3);
x_165 = lean_ctor_get(x_67, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_166 = x_67;
} else {
 lean_dec_ref(x_67);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_147, 1);
lean_inc(x_167);
lean_dec(x_147);
x_168 = lean_array_get_size(x_167);
x_169 = lean_nat_dec_lt(x_65, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_65);
lean_dec(x_1);
x_170 = l_Lean_IR_Checker_checkExpr___closed__4;
if (lean_is_scalar(x_166)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_166;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
return x_171;
}
else
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_array_fget(x_167, x_65);
lean_dec(x_65);
lean_dec(x_167);
x_173 = l_Lean_IR_IRType_beq(x_172, x_1);
lean_dec(x_1);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_166)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_166;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_165);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_166)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_166;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_165);
return x_177;
}
}
}
default: 
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_65);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_67, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_179 = x_67;
} else {
 lean_dec_ref(x_67);
 x_179 = lean_box(0);
}
x_180 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_147);
x_181 = l_Std_Format_defWidth;
x_182 = lean_format_pretty(x_180, x_181);
x_183 = l_Lean_IR_Checker_checkExpr___closed__2;
x_184 = lean_string_append(x_183, x_182);
lean_dec(x_182);
x_185 = l_Lean_IR_Checker_getDecl___closed__2;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_186);
if (lean_is_scalar(x_179)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_179;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_178);
return x_188;
}
}
}
}
}
case 4:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
lean_dec(x_2);
x_190 = l_Lean_IR_Checker_checkObjVar(x_189, x_3, x_4);
lean_dec(x_3);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_190, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_191);
if (x_194 == 0)
{
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_191, 0);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_190, 0, x_196);
return x_190;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_190, 1);
lean_inc(x_197);
lean_dec(x_190);
x_198 = lean_ctor_get(x_191, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_199 = x_191;
} else {
 lean_dec_ref(x_191);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
}
else
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_191);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_191, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_190);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_190, 0);
lean_dec(x_205);
x_206 = lean_box(5);
x_207 = l_Lean_IR_IRType_beq(x_1, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_209 = l_Std_Format_defWidth;
x_210 = lean_format_pretty(x_208, x_209);
x_211 = l_Lean_IR_Checker_checkType___closed__1;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = l_Lean_IR_Checker_getDecl___closed__2;
x_214 = lean_string_append(x_212, x_213);
lean_ctor_set_tag(x_191, 0);
lean_ctor_set(x_191, 0, x_214);
return x_190;
}
else
{
lean_object* x_215; 
lean_free_object(x_191);
lean_dec(x_1);
x_215 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_190, 0, x_215);
return x_190;
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = lean_ctor_get(x_190, 1);
lean_inc(x_216);
lean_dec(x_190);
x_217 = lean_box(5);
x_218 = l_Lean_IR_IRType_beq(x_1, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_219 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_220 = l_Std_Format_defWidth;
x_221 = lean_format_pretty(x_219, x_220);
x_222 = l_Lean_IR_Checker_checkType___closed__1;
x_223 = lean_string_append(x_222, x_221);
lean_dec(x_221);
x_224 = l_Lean_IR_Checker_getDecl___closed__2;
x_225 = lean_string_append(x_223, x_224);
lean_ctor_set_tag(x_191, 0);
lean_ctor_set(x_191, 0, x_225);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_191);
lean_ctor_set(x_226, 1, x_216);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_free_object(x_191);
lean_dec(x_1);
x_227 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_216);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_191);
x_229 = lean_ctor_get(x_190, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_230 = x_190;
} else {
 lean_dec_ref(x_190);
 x_230 = lean_box(0);
}
x_231 = lean_box(5);
x_232 = l_Lean_IR_IRType_beq(x_1, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_233 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_234 = l_Std_Format_defWidth;
x_235 = lean_format_pretty(x_233, x_234);
x_236 = l_Lean_IR_Checker_checkType___closed__1;
x_237 = lean_string_append(x_236, x_235);
lean_dec(x_235);
x_238 = l_Lean_IR_Checker_getDecl___closed__2;
x_239 = lean_string_append(x_237, x_238);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
if (lean_is_scalar(x_230)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_230;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_229);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_1);
x_242 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_230)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_230;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_229);
return x_243;
}
}
}
}
case 5:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_2, 2);
lean_inc(x_244);
lean_dec(x_2);
x_245 = l_Lean_IR_Checker_checkObjVar(x_244, x_3, x_4);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; 
lean_dec(x_3);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_245);
if (x_247 == 0)
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_245, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_246);
if (x_249 == 0)
{
return x_245;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_246, 0);
lean_inc(x_250);
lean_dec(x_246);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_245, 0, x_251);
return x_245;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_245, 1);
lean_inc(x_252);
lean_dec(x_245);
x_253 = lean_ctor_get(x_246, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_254 = x_246;
} else {
 lean_dec_ref(x_246);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_252);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_246);
x_257 = lean_ctor_get(x_245, 1);
lean_inc(x_257);
lean_dec(x_245);
x_258 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_257);
lean_dec(x_3);
return x_258;
}
}
case 6:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_1);
x_259 = lean_ctor_get(x_2, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_2, 1);
lean_inc(x_260);
lean_dec(x_2);
x_261 = l_Lean_IR_Checker_checkFullApp(x_259, x_260, x_3, x_4);
lean_dec(x_260);
return x_261;
}
case 7:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_2, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_2, 1);
lean_inc(x_263);
lean_dec(x_2);
lean_inc(x_3);
x_264 = l_Lean_IR_Checker_checkPartialApp(x_262, x_263, x_3, x_4);
lean_dec(x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
uint8_t x_266; 
lean_dec(x_3);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_264);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_264, 0);
lean_dec(x_267);
x_268 = !lean_is_exclusive(x_265);
if (x_268 == 0)
{
return x_264;
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
lean_dec(x_265);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_264, 0, x_270);
return x_264;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_271 = lean_ctor_get(x_264, 1);
lean_inc(x_271);
lean_dec(x_264);
x_272 = lean_ctor_get(x_265, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_273 = x_265;
} else {
 lean_dec_ref(x_265);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_271);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_265);
x_276 = lean_ctor_get(x_264, 1);
lean_inc(x_276);
lean_dec(x_264);
x_277 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_276);
lean_dec(x_3);
return x_277;
}
}
case 8:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_1);
x_278 = lean_ctor_get(x_2, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_2, 1);
lean_inc(x_279);
lean_dec(x_2);
x_280 = l_Lean_IR_Checker_checkObjVar(x_278, x_3, x_4);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
lean_dec(x_279);
lean_dec(x_3);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_280, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_281);
if (x_284 == 0)
{
return x_280;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_280, 0, x_286);
return x_280;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_280, 1);
lean_inc(x_287);
lean_dec(x_280);
x_288 = lean_ctor_get(x_281, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_289 = x_281;
} else {
 lean_dec_ref(x_281);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 1, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_288);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_281);
x_292 = lean_ctor_get(x_280, 1);
lean_inc(x_292);
lean_dec(x_280);
x_293 = l_Lean_IR_Checker_checkArgs(x_279, x_3, x_292);
lean_dec(x_279);
return x_293;
}
}
case 9:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_361; lean_object* x_362; 
x_294 = lean_ctor_get(x_2, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_2, 1);
lean_inc(x_295);
lean_dec(x_2);
x_361 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 0)
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_361);
if (x_363 == 0)
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_361, 0);
lean_dec(x_364);
x_365 = !lean_is_exclusive(x_362);
if (x_365 == 0)
{
x_296 = x_361;
goto block_360;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_362, 0);
lean_inc(x_366);
lean_dec(x_362);
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_361, 0, x_367);
x_296 = x_361;
goto block_360;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_368 = lean_ctor_get(x_361, 1);
lean_inc(x_368);
lean_dec(x_361);
x_369 = lean_ctor_get(x_362, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_370 = x_362;
} else {
 lean_dec_ref(x_362);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 1, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_369);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_368);
x_296 = x_372;
goto block_360;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_362);
x_373 = lean_ctor_get(x_361, 1);
lean_inc(x_373);
lean_dec(x_361);
lean_inc(x_295);
x_374 = l_Lean_IR_Checker_checkScalarVar(x_295, x_3, x_373);
x_296 = x_374;
goto block_360;
}
block_360:
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
uint8_t x_298; 
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_3);
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
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_297);
x_308 = lean_ctor_get(x_296, 1);
lean_inc(x_308);
lean_dec(x_296);
x_309 = l_Lean_IR_Checker_getType(x_295, x_3, x_308);
lean_dec(x_3);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_obj_tag(x_310) == 0)
{
uint8_t x_311; 
lean_dec(x_294);
x_311 = !lean_is_exclusive(x_309);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_309, 0);
lean_dec(x_312);
x_313 = !lean_is_exclusive(x_310);
if (x_313 == 0)
{
return x_309;
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_310, 0);
lean_inc(x_314);
lean_dec(x_310);
x_315 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_309, 0, x_315);
return x_309;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_316 = lean_ctor_get(x_309, 1);
lean_inc(x_316);
lean_dec(x_309);
x_317 = lean_ctor_get(x_310, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_318 = x_310;
} else {
 lean_dec_ref(x_310);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(0, 1, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_317);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_316);
return x_320;
}
}
else
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_309);
if (x_321 == 0)
{
lean_object* x_322; uint8_t x_323; 
x_322 = lean_ctor_get(x_309, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_310);
if (x_323 == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_310, 0);
x_325 = l_Lean_IR_IRType_beq(x_324, x_294);
lean_dec(x_294);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_326 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_324);
x_327 = l_Std_Format_defWidth;
x_328 = lean_format_pretty(x_326, x_327);
x_329 = l_Lean_IR_Checker_checkType___closed__1;
x_330 = lean_string_append(x_329, x_328);
lean_dec(x_328);
x_331 = l_Lean_IR_Checker_getDecl___closed__2;
x_332 = lean_string_append(x_330, x_331);
lean_ctor_set_tag(x_310, 0);
lean_ctor_set(x_310, 0, x_332);
return x_309;
}
else
{
lean_object* x_333; 
lean_free_object(x_310);
lean_dec(x_324);
x_333 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_309, 0, x_333);
return x_309;
}
}
else
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_ctor_get(x_310, 0);
lean_inc(x_334);
lean_dec(x_310);
x_335 = l_Lean_IR_IRType_beq(x_334, x_294);
lean_dec(x_294);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_336 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_334);
x_337 = l_Std_Format_defWidth;
x_338 = lean_format_pretty(x_336, x_337);
x_339 = l_Lean_IR_Checker_checkType___closed__1;
x_340 = lean_string_append(x_339, x_338);
lean_dec(x_338);
x_341 = l_Lean_IR_Checker_getDecl___closed__2;
x_342 = lean_string_append(x_340, x_341);
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_309, 0, x_343);
return x_309;
}
else
{
lean_object* x_344; 
lean_dec(x_334);
x_344 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_309, 0, x_344);
return x_309;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_309, 1);
lean_inc(x_345);
lean_dec(x_309);
x_346 = lean_ctor_get(x_310, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_347 = x_310;
} else {
 lean_dec_ref(x_310);
 x_347 = lean_box(0);
}
x_348 = l_Lean_IR_IRType_beq(x_346, x_294);
lean_dec(x_294);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_346);
x_350 = l_Std_Format_defWidth;
x_351 = lean_format_pretty(x_349, x_350);
x_352 = l_Lean_IR_Checker_checkType___closed__1;
x_353 = lean_string_append(x_352, x_351);
lean_dec(x_351);
x_354 = l_Lean_IR_Checker_getDecl___closed__2;
x_355 = lean_string_append(x_353, x_354);
if (lean_is_scalar(x_347)) {
 x_356 = lean_alloc_ctor(0, 1, 0);
} else {
 x_356 = x_347;
 lean_ctor_set_tag(x_356, 0);
}
lean_ctor_set(x_356, 0, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_345);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_347);
lean_dec(x_346);
x_358 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_345);
return x_359;
}
}
}
}
}
}
case 10:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_2, 0);
lean_inc(x_375);
lean_dec(x_2);
x_376 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
uint8_t x_378; 
lean_dec(x_375);
lean_dec(x_3);
x_378 = !lean_is_exclusive(x_376);
if (x_378 == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = lean_ctor_get(x_376, 0);
lean_dec(x_379);
x_380 = !lean_is_exclusive(x_377);
if (x_380 == 0)
{
return x_376;
}
else
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_377, 0);
lean_inc(x_381);
lean_dec(x_377);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_376, 0, x_382);
return x_376;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_376, 1);
lean_inc(x_383);
lean_dec(x_376);
x_384 = lean_ctor_get(x_377, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_385 = x_377;
} else {
 lean_dec_ref(x_377);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(0, 1, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_384);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_383);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; 
lean_dec(x_377);
x_388 = lean_ctor_get(x_376, 1);
lean_inc(x_388);
lean_dec(x_376);
x_389 = l_Lean_IR_Checker_checkObjVar(x_375, x_3, x_388);
lean_dec(x_3);
return x_389;
}
}
case 11:
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_2, 0);
lean_inc(x_390);
lean_dec(x_2);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_390);
lean_dec(x_3);
lean_dec(x_1);
x_391 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_4);
return x_392;
}
else
{
lean_object* x_393; 
lean_dec(x_390);
x_393 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
lean_dec(x_3);
return x_393;
}
}
default: 
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_2, 0);
lean_inc(x_394);
lean_dec(x_2);
x_395 = l_Lean_IR_Checker_checkObjVar(x_394, x_3, x_4);
lean_dec(x_3);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
uint8_t x_397; 
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_395);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_ctor_get(x_395, 0);
lean_dec(x_398);
x_399 = !lean_is_exclusive(x_396);
if (x_399 == 0)
{
return x_395;
}
else
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
lean_dec(x_396);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_395, 0, x_401);
return x_395;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_395, 1);
lean_inc(x_402);
lean_dec(x_395);
x_403 = lean_ctor_get(x_396, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_404 = x_396;
} else {
 lean_dec_ref(x_396);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(0, 1, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_403);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_402);
return x_406;
}
}
else
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_396);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_ctor_get(x_396, 0);
lean_dec(x_408);
x_409 = !lean_is_exclusive(x_395);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_410 = lean_ctor_get(x_395, 0);
lean_dec(x_410);
x_411 = lean_box(1);
x_412 = l_Lean_IR_IRType_beq(x_1, x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_413 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_414 = l_Std_Format_defWidth;
x_415 = lean_format_pretty(x_413, x_414);
x_416 = l_Lean_IR_Checker_checkType___closed__1;
x_417 = lean_string_append(x_416, x_415);
lean_dec(x_415);
x_418 = l_Lean_IR_Checker_getDecl___closed__2;
x_419 = lean_string_append(x_417, x_418);
lean_ctor_set_tag(x_396, 0);
lean_ctor_set(x_396, 0, x_419);
return x_395;
}
else
{
lean_object* x_420; 
lean_free_object(x_396);
lean_dec(x_1);
x_420 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_395, 0, x_420);
return x_395;
}
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_421 = lean_ctor_get(x_395, 1);
lean_inc(x_421);
lean_dec(x_395);
x_422 = lean_box(1);
x_423 = l_Lean_IR_IRType_beq(x_1, x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_424 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_425 = l_Std_Format_defWidth;
x_426 = lean_format_pretty(x_424, x_425);
x_427 = l_Lean_IR_Checker_checkType___closed__1;
x_428 = lean_string_append(x_427, x_426);
lean_dec(x_426);
x_429 = l_Lean_IR_Checker_getDecl___closed__2;
x_430 = lean_string_append(x_428, x_429);
lean_ctor_set_tag(x_396, 0);
lean_ctor_set(x_396, 0, x_430);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_396);
lean_ctor_set(x_431, 1, x_421);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; 
lean_free_object(x_396);
lean_dec(x_1);
x_432 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_421);
return x_433;
}
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
lean_dec(x_396);
x_434 = lean_ctor_get(x_395, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_435 = x_395;
} else {
 lean_dec_ref(x_395);
 x_435 = lean_box(0);
}
x_436 = lean_box(1);
x_437 = l_Lean_IR_IRType_beq(x_1, x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_438 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_439 = l_Std_Format_defWidth;
x_440 = lean_format_pretty(x_438, x_439);
x_441 = l_Lean_IR_Checker_checkType___closed__1;
x_442 = lean_string_append(x_441, x_440);
lean_dec(x_440);
x_443 = l_Lean_IR_Checker_getDecl___closed__2;
x_444 = lean_string_append(x_442, x_443);
x_445 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_445, 0, x_444);
if (lean_is_scalar(x_435)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_435;
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_434);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_1);
x_447 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_435)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_435;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_434);
return x_448;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 == x_3;
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
x_25 = x_2 + x_24;
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
x_7 = x_2 == x_3;
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
x_25 = x_2 + x_24;
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
lean_object* x_60; lean_object* x_61; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_49);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
x_88 = lean_array_get_size(x_45);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_nat_dec_lt(x_89, x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_88);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_86);
lean_ctor_set(x_91, 2, x_87);
lean_inc(x_46);
x_92 = l_Lean_IR_Checker_checkFnBody(x_46, x_91, x_60);
x_61 = x_92;
goto block_84;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_88, x_88);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_88);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_86);
lean_ctor_set(x_94, 2, x_87);
lean_inc(x_46);
x_95 = l_Lean_IR_Checker_checkFnBody(x_46, x_94, x_60);
x_61 = x_95;
goto block_84;
}
else
{
size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = 0;
x_97 = lean_usize_of_nat(x_88);
lean_dec(x_88);
lean_inc(x_2);
x_98 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(x_45, x_96, x_97, x_86, x_2, x_60);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
lean_dec(x_87);
lean_dec(x_85);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
x_61 = x_98;
goto block_84;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_98, 0, x_104);
x_61 = x_98;
goto block_84;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
x_61 = x_109;
goto block_84;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_98, 1);
lean_inc(x_110);
lean_dec(x_98);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_85);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_87);
lean_inc(x_46);
x_113 = l_Lean_IR_Checker_checkFnBody(x_46, x_112, x_110);
x_61 = x_113;
goto block_84;
}
}
}
block_84:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_61, 0, x_67);
return x_61;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
else
{
lean_object* x_73; uint8_t x_74; 
lean_dec(x_62);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
lean_dec(x_61);
x_74 = !lean_is_exclusive(x_2);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_2, 1);
x_76 = l_Lean_IR_LocalContext_addJP(x_75, x_44, x_45, x_46);
lean_ctor_set(x_2, 1, x_76);
x_1 = x_47;
x_3 = x_73;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_2);
x_81 = l_Lean_IR_LocalContext_addJP(x_79, x_44, x_45, x_46);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_80);
x_1 = x_47;
x_2 = x_82;
x_3 = x_73;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_1, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_1, 3);
lean_inc(x_116);
lean_dec(x_1);
x_117 = l_Lean_IR_Checker_checkVar(x_114, x_2, x_3);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_117, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_118);
if (x_121 == 0)
{
return x_117;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_117, 0, x_123);
return x_117;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
lean_dec(x_117);
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_124);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_118);
x_129 = lean_ctor_get(x_117, 1);
lean_inc(x_129);
lean_dec(x_117);
x_130 = l_Lean_IR_Checker_checkArg(x_115, x_2, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
lean_dec(x_116);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_130, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
return x_130;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_130, 0, x_136);
return x_130;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_130, 1);
lean_inc(x_137);
lean_dec(x_130);
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_137);
return x_141;
}
}
else
{
lean_object* x_142; 
lean_dec(x_131);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
lean_dec(x_130);
x_1 = x_116;
x_3 = x_142;
goto _start;
}
}
}
case 4:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_1, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 3);
lean_inc(x_146);
lean_dec(x_1);
x_147 = l_Lean_IR_Checker_checkVar(x_144, x_2, x_3);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_147, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_148);
if (x_151 == 0)
{
return x_147;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_148, 0);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_147, 0, x_153);
return x_147;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_dec(x_147);
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_156 = x_148;
} else {
 lean_dec_ref(x_148);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_148);
x_159 = lean_ctor_get(x_147, 1);
lean_inc(x_159);
lean_dec(x_147);
x_160 = l_Lean_IR_Checker_checkVar(x_145, x_2, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
lean_dec(x_146);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_160);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_160, 0);
lean_dec(x_163);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_161, 0);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_160, 0, x_166);
return x_160;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_168 = lean_ctor_get(x_161, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_167);
return x_171;
}
}
else
{
lean_object* x_172; 
lean_dec(x_161);
x_172 = lean_ctor_get(x_160, 1);
lean_inc(x_172);
lean_dec(x_160);
x_1 = x_146;
x_3 = x_172;
goto _start;
}
}
}
case 5:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_1, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_1, 5);
lean_inc(x_176);
lean_dec(x_1);
x_177 = l_Lean_IR_Checker_checkVar(x_174, x_2, x_3);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_2);
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_177, 0);
lean_dec(x_180);
x_181 = !lean_is_exclusive(x_178);
if (x_181 == 0)
{
return x_177;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
lean_dec(x_178);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_177, 0, x_183);
return x_177;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_177, 1);
lean_inc(x_184);
lean_dec(x_177);
x_185 = lean_ctor_get(x_178, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_186 = x_178;
} else {
 lean_dec_ref(x_178);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_178);
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
lean_dec(x_177);
x_190 = l_Lean_IR_Checker_checkVar(x_175, x_2, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
lean_dec(x_176);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_190, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_191);
if (x_194 == 0)
{
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_191, 0);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_190, 0, x_196);
return x_190;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_190, 1);
lean_inc(x_197);
lean_dec(x_190);
x_198 = lean_ctor_get(x_191, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_199 = x_191;
} else {
 lean_dec_ref(x_191);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
}
else
{
lean_object* x_202; 
lean_dec(x_191);
x_202 = lean_ctor_get(x_190, 1);
lean_inc(x_202);
lean_dec(x_190);
x_1 = x_176;
x_3 = x_202;
goto _start;
}
}
}
case 8:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_1, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_1, 1);
lean_inc(x_205);
lean_dec(x_1);
x_206 = l_Lean_IR_Checker_checkVar(x_204, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
lean_dec(x_205);
lean_dec(x_2);
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_206, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_207);
if (x_210 == 0)
{
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
lean_dec(x_207);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_206, 0, x_212);
return x_206;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_ctor_get(x_207, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_215 = x_207;
} else {
 lean_dec_ref(x_207);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
return x_217;
}
}
else
{
lean_object* x_218; 
lean_dec(x_207);
x_218 = lean_ctor_get(x_206, 1);
lean_inc(x_218);
lean_dec(x_206);
x_1 = x_205;
x_3 = x_218;
goto _start;
}
}
case 9:
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_1, 1);
lean_inc(x_220);
lean_dec(x_1);
x_1 = x_220;
goto _start;
}
case 10:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_1, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_1, 3);
lean_inc(x_223);
lean_dec(x_1);
x_224 = l_Lean_IR_Checker_checkVar(x_222, x_2, x_3);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
lean_dec(x_223);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_224);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_224, 0);
lean_dec(x_227);
x_228 = !lean_is_exclusive(x_225);
if (x_228 == 0)
{
return x_224;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_225, 0);
lean_inc(x_229);
lean_dec(x_225);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_224, 0, x_230);
return x_224;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_224, 1);
lean_inc(x_231);
lean_dec(x_224);
x_232 = lean_ctor_get(x_225, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_233 = x_225;
} else {
 lean_dec_ref(x_225);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_231);
return x_235;
}
}
else
{
uint8_t x_236; 
lean_dec(x_225);
x_236 = !lean_is_exclusive(x_224);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_224, 1);
x_238 = lean_ctor_get(x_224, 0);
lean_dec(x_238);
x_239 = lean_array_get_size(x_223);
x_240 = lean_unsigned_to_nat(0u);
x_241 = lean_nat_dec_lt(x_240, x_239);
if (x_241 == 0)
{
lean_object* x_242; 
lean_dec(x_239);
lean_dec(x_223);
lean_dec(x_2);
x_242 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_224, 0, x_242);
return x_224;
}
else
{
uint8_t x_243; 
x_243 = lean_nat_dec_le(x_239, x_239);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_239);
lean_dec(x_223);
lean_dec(x_2);
x_244 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_224, 0, x_244);
return x_224;
}
else
{
size_t x_245; size_t x_246; lean_object* x_247; lean_object* x_248; 
lean_free_object(x_224);
x_245 = 0;
x_246 = lean_usize_of_nat(x_239);
lean_dec(x_239);
x_247 = lean_box(0);
x_248 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(x_223, x_245, x_246, x_247, x_2, x_237);
lean_dec(x_223);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_224, 1);
lean_inc(x_249);
lean_dec(x_224);
x_250 = lean_array_get_size(x_223);
x_251 = lean_unsigned_to_nat(0u);
x_252 = lean_nat_dec_lt(x_251, x_250);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_250);
lean_dec(x_223);
lean_dec(x_2);
x_253 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_249);
return x_254;
}
else
{
uint8_t x_255; 
x_255 = lean_nat_dec_le(x_250, x_250);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_250);
lean_dec(x_223);
lean_dec(x_2);
x_256 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_249);
return x_257;
}
else
{
size_t x_258; size_t x_259; lean_object* x_260; lean_object* x_261; 
x_258 = 0;
x_259 = lean_usize_of_nat(x_250);
lean_dec(x_250);
x_260 = lean_box(0);
x_261 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(x_223, x_258, x_259, x_260, x_2, x_249);
lean_dec(x_223);
return x_261;
}
}
}
}
}
case 11:
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_1, 0);
lean_inc(x_262);
lean_dec(x_1);
x_263 = l_Lean_IR_Checker_checkArg(x_262, x_2, x_3);
lean_dec(x_2);
return x_263;
}
case 12:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_1, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_1, 1);
lean_inc(x_265);
lean_dec(x_1);
x_266 = l_Lean_IR_Checker_checkJP(x_264, x_2, x_3);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
lean_dec(x_265);
lean_dec(x_2);
x_268 = !lean_is_exclusive(x_266);
if (x_268 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_266, 0);
lean_dec(x_269);
x_270 = !lean_is_exclusive(x_267);
if (x_270 == 0)
{
return x_266;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_267, 0);
lean_inc(x_271);
lean_dec(x_267);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_266, 0, x_272);
return x_266;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_266, 1);
lean_inc(x_273);
lean_dec(x_266);
x_274 = lean_ctor_get(x_267, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_275 = x_267;
} else {
 lean_dec_ref(x_267);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_273);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_267);
x_278 = lean_ctor_get(x_266, 1);
lean_inc(x_278);
lean_dec(x_266);
x_279 = l_Lean_IR_Checker_checkArgs(x_265, x_2, x_278);
lean_dec(x_265);
return x_279;
}
}
case 13:
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_2);
x_280 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_3);
return x_281;
}
default: 
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_1, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_1, 2);
lean_inc(x_283);
lean_dec(x_1);
x_284 = l_Lean_IR_Checker_checkVar(x_282, x_2, x_3);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
lean_dec(x_283);
lean_dec(x_2);
x_286 = !lean_is_exclusive(x_284);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_ctor_get(x_284, 0);
lean_dec(x_287);
x_288 = !lean_is_exclusive(x_285);
if (x_288 == 0)
{
return x_284;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
lean_dec(x_285);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_284, 0, x_290);
return x_284;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_284, 1);
lean_inc(x_291);
lean_dec(x_284);
x_292 = lean_ctor_get(x_285, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_293 = x_285;
} else {
 lean_dec_ref(x_285);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(0, 1, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_292);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_291);
return x_295;
}
}
else
{
lean_object* x_296; 
lean_dec(x_285);
x_296 = lean_ctor_get(x_284, 1);
lean_inc(x_296);
lean_dec(x_284);
x_1 = x_283;
x_3 = x_296;
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
x_21 = l_Lean_IR_Checker_checkPartialApp___closed__4;
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
x_39 = l_Lean_IR_Checker_checkPartialApp___closed__4;
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
x_8 = x_3 == x_4;
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
x_14 = x_3 + x_13;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(lean_object* w) {
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
l_Lean_IR_Checker_maxCtorFields___closed__1 = _init_l_Lean_IR_Checker_maxCtorFields___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields___closed__1);
l_Lean_IR_Checker_maxCtorFields = _init_l_Lean_IR_Checker_maxCtorFields();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields);
l_Lean_IR_Checker_maxCtorScalarsSize___closed__1 = _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize___closed__1);
l_Lean_IR_Checker_maxCtorScalarsSize = _init_l_Lean_IR_Checker_maxCtorScalarsSize();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize);
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
l_Lean_IR_Checker_checkPartialApp___closed__4 = _init_l_Lean_IR_Checker_checkPartialApp___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__4);
l_Lean_IR_Checker_checkExpr___lambda__2___closed__1 = _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___lambda__2___closed__1);
l_Lean_IR_Checker_checkExpr___lambda__2___closed__2 = _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___lambda__2___closed__2);
l_Lean_IR_Checker_checkExpr___closed__1 = _init_l_Lean_IR_Checker_checkExpr___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__1);
l_Lean_IR_Checker_checkExpr___closed__2 = _init_l_Lean_IR_Checker_checkExpr___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__2);
l_Lean_IR_Checker_checkExpr___closed__3 = _init_l_Lean_IR_Checker_checkExpr___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__3);
l_Lean_IR_Checker_checkExpr___closed__4 = _init_l_Lean_IR_Checker_checkExpr___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__4);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__1);
l_Lean_IR_checkDecl___closed__2 = _init_l_Lean_IR_checkDecl___closed__2();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
