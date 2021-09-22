// Lean compiler output
// Module: Lean.Compiler.IR.FreeVars
// Imports: Init Lean.Compiler.IR.Basic
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_FreeIndices_insertParams___spec__1(lean_object*, size_t, size_t, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitFnBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitParams___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_MaxIndex_collectFnBody___closed__1;
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_seq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_seq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Expr_hasFreeVar(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Arg_hasFreeVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitJP___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitFnBody___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitArgs___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_FreeIndices_insertParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip(lean_object*);
static lean_object* l_Lean_IR_FreeIndices_collectFnBody___closed__1;
extern lean_object* l_Id_instMonadId;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArgs(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_hasFreeVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_seq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_3);
return x_3;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___rarg___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Id_instMonadId;
x_12 = l_Array_foldlMUnsafe_fold___rarg(x_11, x_4, x_1, x_9, x_10, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__2(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__2(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_3, x_2);
lean_dec(x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_dec_lt(x_2, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_6, x_2);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_6, x_5);
lean_dec(x_6);
return x_9;
}
}
case 5:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
return x_2;
}
else
{
lean_dec(x_2);
return x_10;
}
}
case 6:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_12, x_2);
lean_dec(x_12);
return x_13;
}
case 7:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_14, x_2);
lean_dec(x_14);
return x_15;
}
case 8:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_nat_dec_lt(x_2, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_17, x_2);
lean_dec(x_17);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_17, x_16);
lean_dec(x_17);
return x_20;
}
}
case 10:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
lean_dec(x_2);
return x_21;
}
}
case 11:
{
lean_dec(x_1);
return x_2;
}
case 12:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_2, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
return x_2;
}
else
{
lean_dec(x_2);
return x_23;
}
}
case 13:
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_nat_dec_lt(x_2, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
return x_2;
}
else
{
lean_dec(x_2);
return x_25;
}
}
default: 
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_nat_dec_lt(x_2, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
return x_2;
}
else
{
lean_dec(x_2);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_5);
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__2(x_1, x_2, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_MaxIndex_collectFnBody___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(x_4, x_2);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(x_4, x_3);
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_nat_dec_lt(x_2, x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_16 = l_Lean_IR_MaxIndex_collectFnBody(x_13, x_2);
x_17 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(x_12, x_16);
lean_dec(x_12);
x_1 = x_14;
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_IR_MaxIndex_collectFnBody(x_13, x_11);
x_20 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(x_12, x_19);
lean_dec(x_12);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_nat_dec_lt(x_2, x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_23, x_2);
lean_dec(x_2);
lean_dec(x_23);
x_1 = x_24;
x_2 = x_26;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_23, x_22);
lean_dec(x_22);
lean_dec(x_23);
x_1 = x_24;
x_2 = x_28;
goto _start;
}
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_nat_dec_lt(x_2, x_30);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_30);
x_34 = lean_nat_dec_lt(x_2, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
x_1 = x_32;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_32;
x_2 = x_31;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = lean_nat_dec_lt(x_30, x_31);
if (x_37 == 0)
{
lean_dec(x_31);
x_1 = x_32;
x_2 = x_30;
goto _start;
}
else
{
lean_dec(x_30);
x_1 = x_32;
x_2 = x_31;
goto _start;
}
}
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 5);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_nat_dec_lt(x_2, x_40);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_40);
x_44 = lean_nat_dec_lt(x_2, x_41);
if (x_44 == 0)
{
lean_dec(x_41);
x_1 = x_42;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_42;
x_2 = x_41;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
x_47 = lean_nat_dec_lt(x_40, x_41);
if (x_47 == 0)
{
lean_dec(x_41);
x_1 = x_42;
x_2 = x_40;
goto _start;
}
else
{
lean_dec(x_40);
x_1 = x_42;
x_2 = x_41;
goto _start;
}
}
}
case 8:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_nat_dec_lt(x_2, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
x_1 = x_51;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_51;
x_2 = x_50;
goto _start;
}
}
case 9:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_1 = x_55;
goto _start;
}
case 10:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 3);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_nat_dec_lt(x_2, x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
x_60 = l_Lean_IR_MaxIndex_collectFnBody___closed__1;
x_61 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1(x_60, x_58, x_2);
lean_dec(x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_62 = l_Lean_IR_MaxIndex_collectFnBody___closed__1;
x_63 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___spec__1(x_62, x_58, x_57);
lean_dec(x_58);
return x_63;
}
}
case 11:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_64, x_2);
lean_dec(x_2);
lean_dec(x_64);
return x_65;
}
case 12:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_nat_dec_lt(x_2, x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
x_69 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_67, x_2);
lean_dec(x_67);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_2);
x_70 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___spec__1(x_67, x_66);
lean_dec(x_67);
return x_70;
}
}
case 13:
{
return x_2;
}
default: 
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
lean_dec(x_1);
x_73 = lean_nat_dec_lt(x_2, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
x_1 = x_72;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_72;
x_2 = x_71;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(x_3, x_2);
lean_dec(x_3);
x_6 = l_Lean_IR_MaxIndex_collectFnBody(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___spec__1(x_7, x_2);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_maxIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_IR_MaxIndex_collectFnBody(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_maxIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
x_7 = lean_apply_2(x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
x_7 = lean_apply_2(x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_1, x_5);
x_7 = lean_apply_2(x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_FreeIndices_insertParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_10 = lean_box(0);
x_11 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_7, x_10);
x_2 = x_9;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_FreeIndices_insertParams___spec__1(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_FreeIndices_insertParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_FreeIndices_insertParams___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_FreeIndices_insertParams(x_3, x_1);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_seq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_apply_2(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_apply_3(x_2, x_6, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_4, x_6);
return x_7;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Id_instMonadId;
x_13 = l_Array_foldlMUnsafe_fold___rarg(x_12, x_5, x_1, x_10, x_11, x_4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_7, x_1, x_5);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__2(x_2, x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_6, x_9);
x_11 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_7, x_2, x_10);
lean_dec(x_7);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_7, x_2, x_3);
lean_dec(x_7);
return x_12;
}
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_13, x_15);
return x_16;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
return x_3;
}
}
case 6:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_17, x_2, x_3);
lean_dec(x_17);
return x_18;
}
case 7:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_19, x_2, x_3);
lean_dec(x_19);
return x_20;
}
case 8:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_21, x_24);
x_26 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_22, x_2, x_25);
lean_dec(x_22);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_21);
x_27 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_22, x_2, x_3);
lean_dec(x_22);
return x_27;
}
}
case 10:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_28, x_30);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
return x_3;
}
}
case 11:
{
lean_dec(x_1);
return x_3;
}
case 12:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_32, x_34);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
return x_3;
}
}
case 13:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_36, x_38);
return x_39;
}
else
{
lean_dec(x_37);
lean_dec(x_36);
return x_3;
}
}
default: 
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_40, x_42);
return x_43;
}
else
{
lean_dec(x_41);
lean_dec(x_40);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
lean_inc(x_1);
lean_inc(x_2);
x_10 = lean_apply_3(x_1, x_9, x_2, x_6);
x_11 = 1;
x_12 = x_4 + x_11;
x_4 = x_12;
x_6 = x_10;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__2(x_1, x_3, x_2, x_9, x_10, x_4);
lean_dec(x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__1(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_FreeIndices_collectFnBody___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(x_5, x_2, x_3);
x_8 = lean_box(0);
x_9 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_4, x_8);
x_1 = x_6;
x_2 = x_9;
x_3 = x_7;
goto _start;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_2);
x_15 = l_Lean_IR_FreeIndices_insertParams(x_2, x_12);
x_16 = l_Lean_IR_FreeIndices_collectFnBody(x_13, x_15, x_3);
x_17 = lean_box(0);
x_18 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_11, x_17);
x_1 = x_14;
x_2 = x_18;
x_3 = x_16;
goto _start;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_20, x_24);
x_26 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_21, x_2, x_25);
x_1 = x_22;
x_3 = x_26;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_20);
x_28 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_21, x_2, x_3);
x_1 = x_22;
x_3 = x_28;
goto _start;
}
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_box(0);
x_35 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_30, x_34);
x_36 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_35, x_31, x_34);
x_1 = x_32;
x_3 = x_37;
goto _start;
}
else
{
lean_dec(x_36);
lean_dec(x_31);
x_1 = x_32;
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_30);
x_40 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_31);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_31, x_41);
x_1 = x_32;
x_3 = x_42;
goto _start;
}
else
{
lean_dec(x_40);
lean_dec(x_31);
x_1 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 5);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_box(0);
x_50 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_45, x_49);
x_51 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_50, x_46, x_49);
x_1 = x_47;
x_3 = x_52;
goto _start;
}
else
{
lean_dec(x_51);
lean_dec(x_46);
x_1 = x_47;
x_3 = x_50;
goto _start;
}
}
else
{
lean_object* x_55; 
lean_dec(x_48);
lean_dec(x_45);
x_55 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_46);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_46, x_56);
x_1 = x_47;
x_3 = x_57;
goto _start;
}
else
{
lean_dec(x_55);
lean_dec(x_46);
x_1 = x_47;
goto _start;
}
}
}
case 8:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
lean_dec(x_1);
x_62 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(0);
x_64 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_60, x_63);
x_1 = x_61;
x_3 = x_64;
goto _start;
}
else
{
lean_dec(x_62);
lean_dec(x_60);
x_1 = x_61;
goto _start;
}
}
case 9:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_1 = x_67;
goto _start;
}
case 10:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 3);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_box(0);
x_73 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_69, x_72);
x_74 = l_Lean_IR_FreeIndices_collectFnBody___closed__1;
x_75 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__1(x_74, x_70, x_2, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_71);
lean_dec(x_69);
x_76 = l_Lean_IR_FreeIndices_collectFnBody___closed__1;
x_77 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___spec__1(x_76, x_70, x_2, x_3);
return x_77;
}
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
lean_dec(x_1);
x_79 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_78, x_2, x_3);
lean_dec(x_2);
return x_79;
}
case 12:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_82 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_box(0);
x_84 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_80, x_83);
x_85 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_81, x_2, x_84);
lean_dec(x_2);
lean_dec(x_81);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_82);
lean_dec(x_80);
x_86 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___spec__1(x_81, x_2, x_3);
lean_dec(x_2);
lean_dec(x_81);
return x_86;
}
}
case 13:
{
lean_dec(x_2);
return x_3;
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
lean_dec(x_1);
x_89 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_2, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_box(0);
x_91 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_3, x_87, x_90);
x_1 = x_88;
x_3 = x_91;
goto _start;
}
else
{
lean_dec(x_89);
lean_dec(x_87);
x_1 = x_88;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_IR_FreeIndices_collectFnBody(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_freeIndices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitJP(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_nat_dec_eq(x_1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitArgs___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_IR_HasIndex_visitArg(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_2, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitArgs___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitArgs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitParams___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_nat_dec_eq(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitParams___spec__1(x_1, x_2, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitParams___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_IR_HasIndex_visitArgs(x_1, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_1, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_IR_HasIndex_visitArgs(x_1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
case 5:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_nat_dec_eq(x_1, x_10);
return x_11;
}
case 6:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Lean_IR_HasIndex_visitArgs(x_1, x_12);
return x_13;
}
case 7:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_Lean_IR_HasIndex_visitArgs(x_1, x_14);
return x_15;
}
case 8:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_nat_dec_eq(x_1, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_IR_HasIndex_visitArgs(x_1, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
case 10:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_nat_dec_eq(x_1, x_21);
return x_22;
}
case 11:
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
case 12:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_nat_dec_eq(x_1, x_24);
return x_25;
}
case 13:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_nat_dec_eq(x_1, x_26);
return x_27;
}
default: 
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_nat_dec_eq(x_1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitExpr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitFnBody___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_8 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_IR_HasIndex_visitExpr(x_1, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 1;
return x_7;
}
}
case 1:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_8);
if (x_10 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_9);
x_12 = 1;
return x_12;
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_nat_dec_eq(x_1, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_IR_HasIndex_visitArg(x_1, x_14);
lean_dec(x_14);
if (x_17 == 0)
{
x_2 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 1;
return x_20;
}
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_nat_dec_eq(x_1, x_21);
lean_dec(x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_1, x_22);
lean_dec(x_22);
if (x_25 == 0)
{
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_23);
x_27 = 1;
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_22);
x_28 = 1;
return x_28;
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 5);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_nat_dec_eq(x_1, x_29);
lean_dec(x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_1, x_30);
lean_dec(x_30);
if (x_33 == 0)
{
x_2 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_31);
x_35 = 1;
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_31);
lean_dec(x_30);
x_36 = 1;
return x_36;
}
}
case 8:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_nat_dec_eq(x_1, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
x_2 = x_38;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_38);
x_41 = 1;
return x_41;
}
}
case 9:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
x_2 = x_42;
goto _start;
}
case 10:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 3);
lean_inc(x_45);
lean_dec(x_2);
x_46 = lean_nat_dec_eq(x_1, x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_47);
lean_dec(x_45);
x_50 = 0;
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_47, x_47);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_47);
lean_dec(x_45);
x_52 = 0;
return x_52;
}
else
{
size_t x_53; size_t x_54; uint8_t x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_55 = l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitFnBody___spec__1(x_1, x_45, x_53, x_54);
lean_dec(x_45);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_45);
x_56 = 1;
return x_56;
}
}
case 11:
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Lean_IR_HasIndex_visitArg(x_1, x_57);
lean_dec(x_57);
return x_58;
}
case 12:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_nat_dec_eq(x_1, x_59);
lean_dec(x_59);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_IR_HasIndex_visitArgs(x_1, x_60);
lean_dec(x_60);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_60);
x_63 = 1;
return x_63;
}
}
case 13:
{
uint8_t x_64; 
x_64 = 0;
return x_64;
}
default: 
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
lean_dec(x_2);
x_67 = lean_nat_dec_eq(x_1, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
x_2 = x_66;
goto _start;
}
else
{
uint8_t x_69; 
lean_dec(x_66);
x_69 = 1;
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_HasIndex_visitFnBody___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitFnBody___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_hasFreeVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_HasIndex_visitArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_hasFreeVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Arg_hasFreeVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_hasFreeVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_HasIndex_visitExpr(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_hasFreeVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Expr_hasFreeVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_hasFreeVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_HasIndex_visitFnBody(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_hasFreeVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_FnBody_hasFreeVar(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_FreeVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_MaxIndex_collectFnBody___closed__1 = _init_l_Lean_IR_MaxIndex_collectFnBody___closed__1();
lean_mark_persistent(l_Lean_IR_MaxIndex_collectFnBody___closed__1);
l_Lean_IR_FreeIndices_collectFnBody___closed__1 = _init_l_Lean_IR_FreeIndices_collectFnBody___closed__1();
lean_mark_persistent(l_Lean_IR_FreeIndices_collectFnBody___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
