// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.Format
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_IR_Checker_getDecl___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__4;
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorTag___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Checker_checkFnBody___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_checkDecl___closed__1;
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
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
x_1 = lean_mk_string_unchecked("variable / joinpoint index ", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has already been used", 22, 22);
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
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_10 = l_Lean_IR_Checker_markIndex___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Checker_markIndex___closed__2;
x_13 = lean_string_append(x_11, x_12);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_16 = l_Lean_IR_Checker_markIndex___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_Checker_markIndex___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_getDecl___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depends on declaration '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', which has no executable code; consider marking definition as 'noncomputable'", 79, 79);
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
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = 1;
x_8 = l_Lean_IR_Checker_getDecl___closed__1;
x_9 = l_Lean_Name_toString(x_1, x_7, x_8);
x_10 = l_Lean_IR_Checker_getDecl___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Checker_getDecl___closed__3;
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
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Checker_getDecl___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x_", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown variable '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
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
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_8 = l_Lean_IR_Checker_checkVar___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_Checker_checkVar___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Checker_checkVar___closed__3;
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
x_1 = lean_mk_string_unchecked("block_", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkJP___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown join point '", 20, 20);
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
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_7 = l_Lean_IR_Checker_checkJP___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_Checker_checkJP___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_checkVar___closed__3;
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
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
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
x_1 = lean_mk_string_unchecked("unexpected type '", 17, 17);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_9 = l_Std_Format_defWidth;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_format_pretty(x_8, x_9, x_10, x_10);
x_12 = l_Lean_IR_Checker_checkType___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_IR_Checker_checkVar___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_Checker_checkType___closed__2;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_apply_4(x_16, x_15, x_17, x_4, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = l_Lean_IR_Checker_checkType___closed__3;
x_21 = lean_string_append(x_20, x_15);
lean_dec(x_15);
x_22 = l_Lean_IR_Checker_checkType___closed__4;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_19);
x_25 = lean_string_append(x_24, x_20);
x_26 = lean_box(0);
x_27 = lean_apply_4(x_16, x_25, x_26, x_4, x_5);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_1);
x_28 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
return x_29;
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
x_1 = lean_mk_string_unchecked("object expected", 15, 15);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = l_Std_Format_defWidth;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = l_Lean_IR_Checker_checkType___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_checkVar___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_Checker_checkType___closed__2;
x_14 = l_Lean_IR_Checker_checkType___closed__3;
x_15 = lean_string_append(x_14, x_12);
lean_dec(x_12);
x_16 = l_Lean_IR_Checker_checkType___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_Checker_checkObjType___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_14);
x_21 = lean_box(0);
x_22 = lean_apply_4(x_13, x_20, x_21, x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkScalarType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scalar expected", 15, 15);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_6 = l_Std_Format_defWidth;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = l_Lean_IR_Checker_checkType___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_checkVar___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_Checker_checkType___closed__2;
x_14 = l_Lean_IR_Checker_checkType___closed__3;
x_15 = lean_string_append(x_14, x_12);
lean_dec(x_12);
x_16 = l_Lean_IR_Checker_checkType___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_Checker_checkScalarType___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_14);
x_21 = lean_box(0);
x_22 = lean_apply_4(x_13, x_20, x_21, x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
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
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_7 = l_Lean_IR_Checker_checkVar___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_Checker_checkVar___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_IR_Checker_checkVar___closed__3;
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
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_6);
x_24 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_21);
x_25 = l_Std_Format_defWidth;
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_format_pretty(x_24, x_25, x_26, x_26);
x_28 = l_Lean_IR_Checker_checkType___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_IR_Checker_checkVar___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_Checker_checkType___closed__2;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_apply_4(x_32, x_31, x_33, x_4, x_19);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = l_Lean_IR_Checker_checkType___closed__3;
x_37 = lean_string_append(x_36, x_31);
lean_dec(x_31);
x_38 = l_Lean_IR_Checker_checkType___closed__4;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_35);
x_41 = lean_string_append(x_40, x_36);
x_42 = lean_box(0);
x_43 = lean_apply_4(x_32, x_41, x_42, x_4, x_19);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_21);
lean_dec(x_4);
x_44 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_6, 0, x_44);
return x_6;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
lean_dec(x_7);
lean_inc(x_46);
x_47 = lean_apply_1(x_2, x_46);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_46);
x_50 = l_Std_Format_defWidth;
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_format_pretty(x_49, x_50, x_51, x_51);
x_53 = l_Lean_IR_Checker_checkType___closed__1;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lean_IR_Checker_checkVar___closed__3;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Lean_IR_Checker_checkType___closed__2;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = lean_apply_4(x_57, x_56, x_58, x_4, x_45);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = l_Lean_IR_Checker_checkType___closed__3;
x_62 = lean_string_append(x_61, x_56);
lean_dec(x_56);
x_63 = l_Lean_IR_Checker_checkType___closed__4;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_60);
x_66 = lean_string_append(x_65, x_61);
x_67 = lean_box(0);
x_68 = lean_apply_4(x_57, x_66, x_67, x_4, x_45);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_46);
lean_dec(x_4);
x_69 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_45);
return x_70;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_4);
x_21 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_22 = l_Std_Format_defWidth;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_format_pretty(x_21, x_22, x_23, x_23);
x_25 = l_Lean_IR_Checker_checkType___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_IR_Checker_checkVar___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_Checker_checkType___closed__2;
x_30 = l_Lean_IR_Checker_checkType___closed__3;
x_31 = lean_string_append(x_30, x_28);
lean_dec(x_28);
x_32 = l_Lean_IR_Checker_checkType___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_IR_Checker_checkObjType___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_30);
x_37 = lean_box(0);
x_38 = lean_apply_4(x_29, x_36, x_37, x_2, x_17);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_19);
lean_dec(x_2);
x_39 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
lean_dec(x_5);
x_42 = l_Lean_IR_IRType_isObj(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_43 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_41);
x_44 = l_Std_Format_defWidth;
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_format_pretty(x_43, x_44, x_45, x_45);
x_47 = l_Lean_IR_Checker_checkType___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_IR_Checker_checkVar___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lean_IR_Checker_checkType___closed__2;
x_52 = l_Lean_IR_Checker_checkType___closed__3;
x_53 = lean_string_append(x_52, x_50);
lean_dec(x_50);
x_54 = l_Lean_IR_Checker_checkType___closed__4;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_IR_Checker_checkObjType___closed__1;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_string_append(x_57, x_52);
x_59 = lean_box(0);
x_60 = lean_apply_4(x_51, x_58, x_59, x_2, x_40);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_2);
x_61 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_40);
return x_62;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_4);
x_21 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_22 = l_Std_Format_defWidth;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_format_pretty(x_21, x_22, x_23, x_23);
x_25 = l_Lean_IR_Checker_checkType___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_IR_Checker_checkVar___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_Checker_checkType___closed__2;
x_30 = l_Lean_IR_Checker_checkType___closed__3;
x_31 = lean_string_append(x_30, x_28);
lean_dec(x_28);
x_32 = l_Lean_IR_Checker_checkType___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_IR_Checker_checkScalarType___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_30);
x_37 = lean_box(0);
x_38 = lean_apply_4(x_29, x_36, x_37, x_2, x_17);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_19);
lean_dec(x_2);
x_39 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
lean_dec(x_5);
x_42 = l_Lean_IR_IRType_isScalar(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_43 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_41);
x_44 = l_Std_Format_defWidth;
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_format_pretty(x_43, x_44, x_45, x_45);
x_47 = l_Lean_IR_Checker_checkType___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_IR_Checker_checkVar___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lean_IR_Checker_checkType___closed__2;
x_52 = l_Lean_IR_Checker_checkType___closed__3;
x_53 = lean_string_append(x_52, x_50);
lean_dec(x_50);
x_54 = l_Lean_IR_Checker_checkType___closed__4;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_IR_Checker_checkScalarType___closed__1;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_string_append(x_57, x_52);
x_59 = lean_box(0);
x_60 = lean_apply_4(x_51, x_58, x_59, x_2, x_40);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_2);
x_61 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_40);
return x_62;
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
x_1 = lean_mk_string_unchecked("incorrect number of arguments to '", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" provided, ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" expected", 9, 9);
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
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_26 = 1;
x_27 = l_Lean_IR_Checker_getDecl___closed__1;
x_28 = l_Lean_Name_toString(x_1, x_26, x_27);
x_29 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_24);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_40 = lean_string_append(x_38, x_39);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_40);
return x_5;
}
else
{
lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_41 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
lean_dec(x_3);
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
x_46 = lean_nat_dec_eq(x_43, x_45);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
x_47 = 1;
x_48 = l_Lean_IR_Checker_getDecl___closed__1;
x_49 = l_Lean_Name_toString(x_1, x_47, x_48);
x_50 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_43);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_5, 0, x_62);
return x_5;
}
else
{
lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_43);
lean_free_object(x_5);
lean_dec(x_1);
x_63 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
lean_dec(x_3);
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
x_70 = lean_nat_dec_eq(x_67, x_69);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_3);
x_71 = 1;
x_72 = l_Lean_IR_Checker_getDecl___closed__1;
x_73 = l_Lean_Name_toString(x_1, x_71, x_72);
x_74 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = l___private_Init_Data_Repr_0__Nat_reprFast(x_67);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = l___private_Init_Data_Repr_0__Nat_reprFast(x_69);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = l_Lean_IR_Checker_checkFullApp___closed__4;
x_85 = lean_string_append(x_83, x_84);
if (lean_is_scalar(x_66)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_66;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_64);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
x_88 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_64);
lean_dec(x_3);
return x_88;
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
lean_dec(x_3);
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
x_1 = lean_mk_string_unchecked("too many arguments too partial application '", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', num. args: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", arity: ", 9, 9);
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
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_26 = 1;
x_27 = l_Lean_IR_Checker_getDecl___closed__1;
x_28 = l_Lean_Name_toString(x_1, x_26, x_27);
x_29 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_24);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lean_IR_Checker_checkType___closed__3;
x_40 = lean_string_append(x_38, x_39);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_40);
return x_5;
}
else
{
lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_1);
x_41 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
lean_dec(x_3);
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
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
x_47 = 1;
x_48 = l_Lean_IR_Checker_getDecl___closed__1;
x_49 = l_Lean_Name_toString(x_1, x_47, x_48);
x_50 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_43);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_IR_Checker_checkType___closed__3;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_5, 0, x_62);
return x_5;
}
else
{
lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_43);
lean_free_object(x_5);
lean_dec(x_1);
x_63 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_18);
lean_dec(x_3);
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
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_3);
x_71 = 1;
x_72 = l_Lean_IR_Checker_getDecl___closed__1;
x_73 = l_Lean_Name_toString(x_1, x_71, x_72);
x_74 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = l___private_Init_Data_Repr_0__Nat_reprFast(x_67);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = l___private_Init_Data_Repr_0__Nat_reprFast(x_69);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = l_Lean_IR_Checker_checkType___closed__3;
x_85 = lean_string_append(x_83, x_84);
if (lean_is_scalar(x_66)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_66;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_64);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
x_88 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_64);
lean_dec(x_3);
return x_88;
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
lean_dec(x_5);
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
x_1 = lean_mk_string_unchecked("constructor '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has too many scalar fields", 28, 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = 1;
x_18 = l_Lean_IR_Checker_getDecl___closed__1;
x_19 = l_Lean_Name_toString(x_16, x_17, x_18);
x_20 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has too many fields", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
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
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = 1;
x_14 = l_Lean_IR_Checker_getDecl___closed__1;
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Lean_IR_Checker_checkExpr___lambda__2___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_Checker_checkExpr___lambda__3___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tag for constructor '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is too big, this is a limitation of the current runtime", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected IR type '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid proj index", 18, 18);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = l_Lean_IR_Checker_maxCtorTag;
x_22 = lean_nat_dec_lt(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = l_Lean_IR_Checker_checkExpr___lambda__3(x_1, x_5, x_6, x_23, x_3, x_4);
lean_dec(x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_5, 2);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_5, 4);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_26, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
x_32 = lean_box(0);
x_33 = l_Lean_IR_Checker_checkExpr___lambda__3(x_1, x_5, x_6, x_32, x_3, x_4);
lean_dec(x_6);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
x_8 = x_34;
goto block_19;
}
}
else
{
lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
x_8 = x_35;
goto block_19;
}
}
else
{
lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_box(0);
x_8 = x_36;
goto block_19;
}
}
block_19:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = 1;
x_11 = l_Lean_IR_Checker_getDecl___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Lean_IR_Checker_checkExpr___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_IR_Checker_checkExpr___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
if (lean_is_scalar(x_7)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_7;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
lean_inc(x_3);
x_38 = l_Lean_IR_Checker_checkObjVar(x_37, x_3, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
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
lean_object* x_50; lean_object* x_51; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_50);
return x_51;
}
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
lean_inc(x_3);
x_54 = l_Lean_IR_Checker_checkObjVar(x_52, x_3, x_4);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_54, 0, x_60);
return x_54;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec(x_54);
x_67 = l_Lean_IR_Checker_checkArgs(x_53, x_3, x_66);
lean_dec(x_53);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
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
lean_object* x_79; lean_object* x_80; 
lean_dec(x_68);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_79);
return x_80;
}
}
}
case 3:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
x_83 = l_Lean_IR_Checker_getType(x_82, x_3, x_4);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec(x_81);
lean_dec(x_3);
lean_dec(x_1);
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
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_84);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_84, 0);
switch (lean_obj_tag(x_96)) {
case 7:
{
lean_object* x_97; lean_object* x_98; 
lean_free_object(x_84);
lean_dec(x_81);
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
lean_dec(x_83);
x_98 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_97);
return x_98;
}
case 8:
{
lean_object* x_99; lean_object* x_100; 
lean_free_object(x_84);
lean_dec(x_81);
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
lean_dec(x_83);
x_100 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_99);
return x_100;
}
case 10:
{
uint8_t x_101; 
lean_free_object(x_84);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_83);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_83, 0);
lean_dec(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_array_get_size(x_103);
x_105 = lean_nat_dec_lt(x_81, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_103);
lean_dec(x_81);
lean_dec(x_1);
x_106 = l_Lean_IR_Checker_checkExpr___closed__5;
lean_ctor_set(x_83, 0, x_106);
return x_83;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_array_fget(x_103, x_81);
lean_dec(x_81);
lean_dec(x_103);
x_108 = l_Lean_IR_IRType_beq(x_107, x_1);
lean_dec(x_1);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_83, 0, x_109);
return x_83;
}
else
{
lean_object* x_110; 
x_110 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_83, 0, x_110);
return x_83;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_83, 1);
lean_inc(x_111);
lean_dec(x_83);
x_112 = lean_ctor_get(x_96, 1);
lean_inc(x_112);
lean_dec(x_96);
x_113 = lean_array_get_size(x_112);
x_114 = lean_nat_dec_lt(x_81, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_112);
lean_dec(x_81);
lean_dec(x_1);
x_115 = l_Lean_IR_Checker_checkExpr___closed__5;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_array_fget(x_112, x_81);
lean_dec(x_81);
lean_dec(x_112);
x_118 = l_Lean_IR_IRType_beq(x_117, x_1);
lean_dec(x_1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_111);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_111);
return x_122;
}
}
}
}
case 11:
{
uint8_t x_123; 
lean_free_object(x_84);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_83);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_83, 0);
lean_dec(x_124);
x_125 = lean_ctor_get(x_96, 1);
lean_inc(x_125);
lean_dec(x_96);
x_126 = lean_array_get_size(x_125);
x_127 = lean_nat_dec_lt(x_81, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_81);
lean_dec(x_1);
x_128 = l_Lean_IR_Checker_checkExpr___closed__5;
lean_ctor_set(x_83, 0, x_128);
return x_83;
}
else
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_array_fget(x_125, x_81);
lean_dec(x_81);
lean_dec(x_125);
x_130 = l_Lean_IR_IRType_beq(x_129, x_1);
lean_dec(x_1);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = l_Lean_IR_Checker_checkEqTypes___closed__2;
lean_ctor_set(x_83, 0, x_131);
return x_83;
}
else
{
lean_object* x_132; 
x_132 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_83, 0, x_132);
return x_83;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_83, 1);
lean_inc(x_133);
lean_dec(x_83);
x_134 = lean_ctor_get(x_96, 1);
lean_inc(x_134);
lean_dec(x_96);
x_135 = lean_array_get_size(x_134);
x_136 = lean_nat_dec_lt(x_81, x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
lean_dec(x_81);
lean_dec(x_1);
x_137 = l_Lean_IR_Checker_checkExpr___closed__5;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
return x_138;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_array_fget(x_134, x_81);
lean_dec(x_81);
lean_dec(x_134);
x_140 = l_Lean_IR_IRType_beq(x_139, x_1);
lean_dec(x_1);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_IR_Checker_checkEqTypes___closed__2;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_133);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_133);
return x_144;
}
}
}
}
default: 
{
uint8_t x_145; 
lean_dec(x_81);
lean_dec(x_3);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_83);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_146 = lean_ctor_get(x_83, 0);
lean_dec(x_146);
x_147 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_96);
x_148 = l_Std_Format_defWidth;
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_format_pretty(x_147, x_148, x_149, x_149);
x_151 = l_Lean_IR_Checker_checkExpr___closed__3;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lean_IR_Checker_checkVar___closed__3;
x_154 = lean_string_append(x_152, x_153);
lean_ctor_set_tag(x_84, 0);
lean_ctor_set(x_84, 0, x_154);
return x_83;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_155 = lean_ctor_get(x_83, 1);
lean_inc(x_155);
lean_dec(x_83);
x_156 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_96);
x_157 = l_Std_Format_defWidth;
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_format_pretty(x_156, x_157, x_158, x_158);
x_160 = l_Lean_IR_Checker_checkExpr___closed__3;
x_161 = lean_string_append(x_160, x_159);
lean_dec(x_159);
x_162 = l_Lean_IR_Checker_checkVar___closed__3;
x_163 = lean_string_append(x_161, x_162);
lean_ctor_set_tag(x_84, 0);
lean_ctor_set(x_84, 0, x_163);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_84);
lean_ctor_set(x_164, 1, x_155);
return x_164;
}
}
}
}
else
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_84, 0);
lean_inc(x_165);
lean_dec(x_84);
switch (lean_obj_tag(x_165)) {
case 7:
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_81);
x_166 = lean_ctor_get(x_83, 1);
lean_inc(x_166);
lean_dec(x_83);
x_167 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_166);
return x_167;
}
case 8:
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_81);
x_168 = lean_ctor_get(x_83, 1);
lean_inc(x_168);
lean_dec(x_83);
x_169 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_168);
return x_169;
}
case 10:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_3);
x_170 = lean_ctor_get(x_83, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_171 = x_83;
} else {
 lean_dec_ref(x_83);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
lean_dec(x_165);
x_173 = lean_array_get_size(x_172);
x_174 = lean_nat_dec_lt(x_81, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_172);
lean_dec(x_81);
lean_dec(x_1);
x_175 = l_Lean_IR_Checker_checkExpr___closed__5;
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_170);
return x_176;
}
else
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_array_fget(x_172, x_81);
lean_dec(x_81);
lean_dec(x_172);
x_178 = l_Lean_IR_IRType_beq(x_177, x_1);
lean_dec(x_1);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_171)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_171;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_170);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_171)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_171;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_170);
return x_182;
}
}
}
case 11:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_3);
x_183 = lean_ctor_get(x_83, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_184 = x_83;
} else {
 lean_dec_ref(x_83);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_165, 1);
lean_inc(x_185);
lean_dec(x_165);
x_186 = lean_array_get_size(x_185);
x_187 = lean_nat_dec_lt(x_81, x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_185);
lean_dec(x_81);
lean_dec(x_1);
x_188 = l_Lean_IR_Checker_checkExpr___closed__5;
if (lean_is_scalar(x_184)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_184;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_183);
return x_189;
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_array_fget(x_185, x_81);
lean_dec(x_81);
lean_dec(x_185);
x_191 = l_Lean_IR_IRType_beq(x_190, x_1);
lean_dec(x_1);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = l_Lean_IR_Checker_checkEqTypes___closed__2;
if (lean_is_scalar(x_184)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_184;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_183);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
if (lean_is_scalar(x_184)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_184;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_183);
return x_195;
}
}
}
default: 
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_81);
lean_dec(x_3);
lean_dec(x_1);
x_196 = lean_ctor_get(x_83, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_197 = x_83;
} else {
 lean_dec_ref(x_83);
 x_197 = lean_box(0);
}
x_198 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_165);
x_199 = l_Std_Format_defWidth;
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_format_pretty(x_198, x_199, x_200, x_200);
x_202 = l_Lean_IR_Checker_checkExpr___closed__3;
x_203 = lean_string_append(x_202, x_201);
lean_dec(x_201);
x_204 = l_Lean_IR_Checker_checkVar___closed__3;
x_205 = lean_string_append(x_203, x_204);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_196);
return x_207;
}
}
}
}
}
case 4:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_2, 1);
lean_inc(x_208);
lean_dec(x_2);
lean_inc(x_3);
x_209 = l_Lean_IR_Checker_checkObjVar(x_208, x_3, x_4);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
lean_dec(x_3);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_209);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_209, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_210);
if (x_213 == 0)
{
return x_209;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
lean_dec(x_210);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_209, 0, x_215);
return x_209;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_209, 1);
lean_inc(x_216);
lean_dec(x_209);
x_217 = lean_ctor_get(x_210, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_218 = x_210;
} else {
 lean_dec_ref(x_210);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 1, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_217);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
return x_220;
}
}
else
{
uint8_t x_221; 
lean_dec(x_210);
x_221 = !lean_is_exclusive(x_209);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_222 = lean_ctor_get(x_209, 1);
x_223 = lean_ctor_get(x_209, 0);
lean_dec(x_223);
x_224 = lean_box(5);
x_225 = l_Lean_IR_IRType_beq(x_1, x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_free_object(x_209);
x_226 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_227 = l_Std_Format_defWidth;
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_format_pretty(x_226, x_227, x_228, x_228);
x_230 = l_Lean_IR_Checker_checkType___closed__1;
x_231 = lean_string_append(x_230, x_229);
lean_dec(x_229);
x_232 = l_Lean_IR_Checker_checkVar___closed__3;
x_233 = lean_string_append(x_231, x_232);
x_234 = l_Lean_IR_Checker_checkType___closed__2;
x_235 = lean_box(0);
x_236 = lean_apply_4(x_234, x_233, x_235, x_3, x_222);
return x_236;
}
else
{
lean_object* x_237; 
lean_dec(x_3);
lean_dec(x_1);
x_237 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_209, 0, x_237);
return x_209;
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_209, 1);
lean_inc(x_238);
lean_dec(x_209);
x_239 = lean_box(5);
x_240 = l_Lean_IR_IRType_beq(x_1, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_241 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_242 = l_Std_Format_defWidth;
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_format_pretty(x_241, x_242, x_243, x_243);
x_245 = l_Lean_IR_Checker_checkType___closed__1;
x_246 = lean_string_append(x_245, x_244);
lean_dec(x_244);
x_247 = l_Lean_IR_Checker_checkVar___closed__3;
x_248 = lean_string_append(x_246, x_247);
x_249 = l_Lean_IR_Checker_checkType___closed__2;
x_250 = lean_box(0);
x_251 = lean_apply_4(x_249, x_248, x_250, x_3, x_238);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_3);
lean_dec(x_1);
x_252 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_238);
return x_253;
}
}
}
}
case 5:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_2, 2);
lean_inc(x_254);
lean_dec(x_2);
lean_inc(x_3);
x_255 = l_Lean_IR_Checker_checkObjVar(x_254, x_3, x_4);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
lean_dec(x_3);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_255);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_255, 0);
lean_dec(x_258);
x_259 = !lean_is_exclusive(x_256);
if (x_259 == 0)
{
return x_255;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_256, 0);
lean_inc(x_260);
lean_dec(x_256);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_255, 0, x_261);
return x_255;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_255, 1);
lean_inc(x_262);
lean_dec(x_255);
x_263 = lean_ctor_get(x_256, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_264 = x_256;
} else {
 lean_dec_ref(x_256);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(0, 1, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_263);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_262);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_256);
x_267 = lean_ctor_get(x_255, 1);
lean_inc(x_267);
lean_dec(x_255);
x_268 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_267);
return x_268;
}
}
case 6:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_1);
x_269 = lean_ctor_get(x_2, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_2, 1);
lean_inc(x_270);
lean_dec(x_2);
x_271 = l_Lean_IR_Checker_checkFullApp(x_269, x_270, x_3, x_4);
lean_dec(x_270);
return x_271;
}
case 7:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_2, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_2, 1);
lean_inc(x_273);
lean_dec(x_2);
lean_inc(x_3);
x_274 = l_Lean_IR_Checker_checkPartialApp(x_272, x_273, x_3, x_4);
lean_dec(x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
uint8_t x_276; 
lean_dec(x_3);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_274);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
x_278 = !lean_is_exclusive(x_275);
if (x_278 == 0)
{
return x_274;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_275, 0);
lean_inc(x_279);
lean_dec(x_275);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_274, 0, x_280);
return x_274;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_274, 1);
lean_inc(x_281);
lean_dec(x_274);
x_282 = lean_ctor_get(x_275, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_283 = x_275;
} else {
 lean_dec_ref(x_275);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_281);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_275);
x_286 = lean_ctor_get(x_274, 1);
lean_inc(x_286);
lean_dec(x_274);
x_287 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_286);
return x_287;
}
}
case 8:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_1);
x_288 = lean_ctor_get(x_2, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_2, 1);
lean_inc(x_289);
lean_dec(x_2);
lean_inc(x_3);
x_290 = l_Lean_IR_Checker_checkObjVar(x_288, x_3, x_4);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
lean_dec(x_289);
lean_dec(x_3);
x_292 = !lean_is_exclusive(x_290);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_290, 0);
lean_dec(x_293);
x_294 = !lean_is_exclusive(x_291);
if (x_294 == 0)
{
return x_290;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_290, 0, x_296);
return x_290;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_297 = lean_ctor_get(x_290, 1);
lean_inc(x_297);
lean_dec(x_290);
x_298 = lean_ctor_get(x_291, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_299 = x_291;
} else {
 lean_dec_ref(x_291);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(0, 1, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_298);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_297);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_291);
x_302 = lean_ctor_get(x_290, 1);
lean_inc(x_302);
lean_dec(x_290);
x_303 = l_Lean_IR_Checker_checkArgs(x_289, x_3, x_302);
lean_dec(x_3);
lean_dec(x_289);
return x_303;
}
}
case 9:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_2, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_2, 1);
lean_inc(x_305);
lean_dec(x_2);
lean_inc(x_3);
x_306 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_3);
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_306, 0);
lean_dec(x_309);
x_310 = !lean_is_exclusive(x_307);
if (x_310 == 0)
{
return x_306;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_307, 0);
lean_inc(x_311);
lean_dec(x_307);
x_312 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_306, 0, x_312);
return x_306;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_313 = lean_ctor_get(x_306, 1);
lean_inc(x_313);
lean_dec(x_306);
x_314 = lean_ctor_get(x_307, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_315 = x_307;
} else {
 lean_dec_ref(x_307);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(0, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_314);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_313);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_307);
x_318 = lean_ctor_get(x_306, 1);
lean_inc(x_318);
lean_dec(x_306);
lean_inc(x_3);
lean_inc(x_305);
x_319 = l_Lean_IR_Checker_checkScalarVar(x_305, x_3, x_318);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_3);
x_321 = !lean_is_exclusive(x_319);
if (x_321 == 0)
{
lean_object* x_322; uint8_t x_323; 
x_322 = lean_ctor_get(x_319, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_320);
if (x_323 == 0)
{
return x_319;
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_320, 0);
lean_inc(x_324);
lean_dec(x_320);
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_319, 0, x_325);
return x_319;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_326 = lean_ctor_get(x_319, 1);
lean_inc(x_326);
lean_dec(x_319);
x_327 = lean_ctor_get(x_320, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_328 = x_320;
} else {
 lean_dec_ref(x_320);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_327);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_326);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_320);
x_331 = lean_ctor_get(x_319, 1);
lean_inc(x_331);
lean_dec(x_319);
x_332 = l_Lean_IR_Checker_getType(x_305, x_3, x_331);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
uint8_t x_334; 
lean_dec(x_304);
lean_dec(x_3);
x_334 = !lean_is_exclusive(x_332);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_332, 0);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_333);
if (x_336 == 0)
{
return x_332;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_333, 0);
lean_inc(x_337);
lean_dec(x_333);
x_338 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_332, 0, x_338);
return x_332;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_332, 1);
lean_inc(x_339);
lean_dec(x_332);
x_340 = lean_ctor_get(x_333, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 x_341 = x_333;
} else {
 lean_dec_ref(x_333);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 1, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_340);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_339);
return x_343;
}
}
else
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_332);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_332, 1);
x_346 = lean_ctor_get(x_332, 0);
lean_dec(x_346);
x_347 = lean_ctor_get(x_333, 0);
lean_inc(x_347);
lean_dec(x_333);
x_348 = l_Lean_IR_IRType_beq(x_347, x_304);
lean_dec(x_304);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_free_object(x_332);
x_349 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_347);
x_350 = l_Std_Format_defWidth;
x_351 = lean_unsigned_to_nat(0u);
x_352 = lean_format_pretty(x_349, x_350, x_351, x_351);
x_353 = l_Lean_IR_Checker_checkType___closed__1;
x_354 = lean_string_append(x_353, x_352);
lean_dec(x_352);
x_355 = l_Lean_IR_Checker_checkVar___closed__3;
x_356 = lean_string_append(x_354, x_355);
x_357 = l_Lean_IR_Checker_checkType___closed__2;
x_358 = lean_box(0);
x_359 = lean_apply_4(x_357, x_356, x_358, x_3, x_345);
return x_359;
}
else
{
lean_object* x_360; 
lean_dec(x_347);
lean_dec(x_3);
x_360 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_332, 0, x_360);
return x_332;
}
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = lean_ctor_get(x_332, 1);
lean_inc(x_361);
lean_dec(x_332);
x_362 = lean_ctor_get(x_333, 0);
lean_inc(x_362);
lean_dec(x_333);
x_363 = l_Lean_IR_IRType_beq(x_362, x_304);
lean_dec(x_304);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_364 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_362);
x_365 = l_Std_Format_defWidth;
x_366 = lean_unsigned_to_nat(0u);
x_367 = lean_format_pretty(x_364, x_365, x_366, x_366);
x_368 = l_Lean_IR_Checker_checkType___closed__1;
x_369 = lean_string_append(x_368, x_367);
lean_dec(x_367);
x_370 = l_Lean_IR_Checker_checkVar___closed__3;
x_371 = lean_string_append(x_369, x_370);
x_372 = l_Lean_IR_Checker_checkType___closed__2;
x_373 = lean_box(0);
x_374 = lean_apply_4(x_372, x_371, x_373, x_3, x_361);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_362);
lean_dec(x_3);
x_375 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_361);
return x_376;
}
}
}
}
}
}
case 10:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_2, 0);
lean_inc(x_377);
lean_dec(x_2);
lean_inc(x_3);
x_378 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
uint8_t x_380; 
lean_dec(x_377);
lean_dec(x_3);
x_380 = !lean_is_exclusive(x_378);
if (x_380 == 0)
{
lean_object* x_381; uint8_t x_382; 
x_381 = lean_ctor_get(x_378, 0);
lean_dec(x_381);
x_382 = !lean_is_exclusive(x_379);
if (x_382 == 0)
{
return x_378;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_379, 0);
lean_inc(x_383);
lean_dec(x_379);
x_384 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_378, 0, x_384);
return x_378;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = lean_ctor_get(x_378, 1);
lean_inc(x_385);
lean_dec(x_378);
x_386 = lean_ctor_get(x_379, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_387 = x_379;
} else {
 lean_dec_ref(x_379);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(0, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_385);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_379);
x_390 = lean_ctor_get(x_378, 1);
lean_inc(x_390);
lean_dec(x_378);
x_391 = l_Lean_IR_Checker_checkObjVar(x_377, x_3, x_390);
return x_391;
}
}
case 11:
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_2, 0);
lean_inc(x_392);
lean_dec(x_2);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_392);
lean_dec(x_3);
lean_dec(x_1);
x_393 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_4);
return x_394;
}
else
{
lean_object* x_395; 
lean_dec(x_392);
x_395 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4);
return x_395;
}
}
default: 
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_2, 0);
lean_inc(x_396);
lean_dec(x_2);
lean_inc(x_3);
x_397 = l_Lean_IR_Checker_checkObjVar(x_396, x_3, x_4);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
if (lean_obj_tag(x_398) == 0)
{
uint8_t x_399; 
lean_dec(x_3);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_397);
if (x_399 == 0)
{
lean_object* x_400; uint8_t x_401; 
x_400 = lean_ctor_get(x_397, 0);
lean_dec(x_400);
x_401 = !lean_is_exclusive(x_398);
if (x_401 == 0)
{
return x_397;
}
else
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
lean_dec(x_398);
x_403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_397, 0, x_403);
return x_397;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_404 = lean_ctor_get(x_397, 1);
lean_inc(x_404);
lean_dec(x_397);
x_405 = lean_ctor_get(x_398, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_406 = x_398;
} else {
 lean_dec_ref(x_398);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 1, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_405);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_404);
return x_408;
}
}
else
{
uint8_t x_409; 
lean_dec(x_398);
x_409 = !lean_is_exclusive(x_397);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_410 = lean_ctor_get(x_397, 1);
x_411 = lean_ctor_get(x_397, 0);
lean_dec(x_411);
x_412 = lean_box(1);
x_413 = l_Lean_IR_IRType_beq(x_1, x_412);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_free_object(x_397);
x_414 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_415 = l_Std_Format_defWidth;
x_416 = lean_unsigned_to_nat(0u);
x_417 = lean_format_pretty(x_414, x_415, x_416, x_416);
x_418 = l_Lean_IR_Checker_checkType___closed__1;
x_419 = lean_string_append(x_418, x_417);
lean_dec(x_417);
x_420 = l_Lean_IR_Checker_checkVar___closed__3;
x_421 = lean_string_append(x_419, x_420);
x_422 = l_Lean_IR_Checker_checkType___closed__2;
x_423 = lean_box(0);
x_424 = lean_apply_4(x_422, x_421, x_423, x_3, x_410);
return x_424;
}
else
{
lean_object* x_425; 
lean_dec(x_3);
lean_dec(x_1);
x_425 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
lean_ctor_set(x_397, 0, x_425);
return x_397;
}
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = lean_ctor_get(x_397, 1);
lean_inc(x_426);
lean_dec(x_397);
x_427 = lean_box(1);
x_428 = l_Lean_IR_IRType_beq(x_1, x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_429 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_430 = l_Std_Format_defWidth;
x_431 = lean_unsigned_to_nat(0u);
x_432 = lean_format_pretty(x_429, x_430, x_431, x_431);
x_433 = l_Lean_IR_Checker_checkType___closed__1;
x_434 = lean_string_append(x_433, x_432);
lean_dec(x_432);
x_435 = l_Lean_IR_Checker_checkVar___closed__3;
x_436 = lean_string_append(x_434, x_435);
x_437 = l_Lean_IR_Checker_checkType___closed__2;
x_438 = lean_box(0);
x_439 = lean_apply_4(x_437, x_436, x_438, x_3, x_426);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_3);
lean_dec(x_1);
x_440 = l_Lean_IR_Checker_markIndex___lambda__1___closed__1;
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_426);
return x_441;
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
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkExpr___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
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
x_10 = l_Lean_IR_Checker_markIndex(x_9, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
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
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_1 = lean_mk_string_unchecked("failed to compile definition, compiler IR check failed at '", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'. Error: ", 10, 10);
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_14 = 1;
x_15 = l_Lean_IR_Checker_getDecl___closed__1;
x_16 = l_Lean_Name_toString(x_13, x_14, x_15);
x_17 = l_Lean_IR_checkDecl___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_IR_checkDecl___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_12);
lean_dec(x_12);
x_22 = l_Lean_IR_Checker_checkType___closed__3;
x_23 = lean_string_append(x_21, x_22);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_1);
lean_inc(x_2);
x_29 = l_Lean_IR_Checker_checkDecl(x_2, x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_IR_Decl_name(x_2);
lean_dec(x_2);
x_33 = 1;
x_34 = l_Lean_IR_Checker_getDecl___closed__1;
x_35 = l_Lean_Name_toString(x_32, x_33, x_34);
x_36 = l_Lean_IR_checkDecl___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_IR_checkDecl___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_31);
lean_dec(x_31);
x_41 = l_Lean_IR_Checker_checkType___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_26);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_30);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_26);
return x_45;
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
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_IR_Checker_getDecl___closed__3 = _init_l_Lean_IR_Checker_getDecl___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__3);
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
l_Lean_IR_Checker_checkVar___closed__3 = _init_l_Lean_IR_Checker_checkVar___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__3);
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
