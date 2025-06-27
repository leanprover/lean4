// Lean compiler output
// Module: Lean.Compiler.IR.FreeVars
// Imports: Lean.Compiler.IR.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Expr_hasFreeVar(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Arg_hasFreeVar(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_seq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0;
lean_object* l_Lean_RBNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitFnBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArgs(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_seq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitParams(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_hasFreeVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_MaxIndex_instAndThenCollector() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_instAndThenCollector___lam__0), 3, 0);
return x_1;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg(x_2, x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0;
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(x_1, x_3, x_2);
return x_4;
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
static lean_object* _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0;
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(x_1, x_3, x_2);
return x_4;
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
lean_object* x_3; lean_object* x_4; lean_object* x_7; lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_3 = x_11;
x_4 = x_2;
goto block_6;
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_nat_dec_lt(x_2, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_13, x_2);
lean_dec(x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_13, x_12);
lean_dec(x_13);
return x_16;
}
}
case 3:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_3 = x_17;
x_4 = x_2;
goto block_6;
}
case 4:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_3 = x_18;
x_4 = x_2;
goto block_6;
}
case 5:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_nat_dec_lt(x_2, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
return x_2;
}
else
{
lean_dec(x_2);
return x_19;
}
}
case 8:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_2, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_22, x_2);
lean_dec(x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_22, x_21);
lean_dec(x_22);
return x_25;
}
}
case 9:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_nat_dec_lt(x_2, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
return x_2;
}
else
{
lean_dec(x_2);
return x_26;
}
}
case 10:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_7 = x_28;
x_8 = x_2;
goto block_10;
}
case 11:
{
lean_dec(x_1);
return x_2;
}
case 12:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_7 = x_29;
x_8 = x_2;
goto block_10;
}
default: 
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_30, x_2);
lean_dec(x_30);
return x_31;
}
}
block_6:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_dec(x_4);
return x_3;
}
}
block_10:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_8);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_2(x_1, x_6, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(x_2, x_4, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_17 = lean_nat_dec_lt(x_2, x_10);
if (x_17 == 0)
{
lean_dec(x_10);
x_13 = x_2;
goto block_16;
}
else
{
lean_dec(x_2);
x_13 = x_10;
goto block_16;
}
block_16:
{
lean_object* x_14; 
x_14 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(x_11, x_13);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_27; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_27 = lean_nat_dec_lt(x_2, x_18);
if (x_27 == 0)
{
lean_dec(x_18);
x_22 = x_2;
goto block_26;
}
else
{
lean_dec(x_2);
x_22 = x_18;
goto block_26;
}
block_26:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_IR_MaxIndex_collectFnBody(x_20, x_22);
x_24 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(x_19, x_23);
lean_dec(x_19);
x_1 = x_21;
x_2 = x_24;
goto _start;
}
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_35; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
lean_dec(x_1);
x_35 = lean_nat_dec_lt(x_2, x_28);
if (x_35 == 0)
{
lean_dec(x_28);
x_31 = x_2;
goto block_34;
}
else
{
lean_dec(x_2);
x_31 = x_28;
goto block_34;
}
block_34:
{
lean_object* x_32; 
x_32 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_1 = x_30;
x_2 = x_32;
goto _start;
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_nat_dec_lt(x_2, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
x_1 = x_37;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_37;
x_2 = x_36;
goto _start;
}
}
case 4:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_49; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_dec(x_1);
x_49 = lean_nat_dec_lt(x_2, x_41);
if (x_49 == 0)
{
lean_dec(x_41);
x_44 = x_2;
goto block_48;
}
else
{
lean_dec(x_2);
x_44 = x_41;
goto block_48;
}
block_48:
{
uint8_t x_45; 
x_45 = lean_nat_dec_lt(x_44, x_42);
if (x_45 == 0)
{
lean_dec(x_42);
x_1 = x_43;
x_2 = x_44;
goto _start;
}
else
{
lean_dec(x_44);
x_1 = x_43;
x_2 = x_42;
goto _start;
}
}
}
case 5:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_58; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 5);
lean_inc(x_52);
lean_dec(x_1);
x_58 = lean_nat_dec_lt(x_2, x_50);
if (x_58 == 0)
{
lean_dec(x_50);
x_53 = x_2;
goto block_57;
}
else
{
lean_dec(x_2);
x_53 = x_50;
goto block_57;
}
block_57:
{
uint8_t x_54; 
x_54 = lean_nat_dec_lt(x_53, x_51);
if (x_54 == 0)
{
lean_dec(x_51);
x_1 = x_52;
x_2 = x_53;
goto _start;
}
else
{
lean_dec(x_53);
x_1 = x_52;
x_2 = x_51;
goto _start;
}
}
}
case 8:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_nat_dec_lt(x_2, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
x_1 = x_60;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_60;
x_2 = x_59;
goto _start;
}
}
case 9:
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_1 = x_64;
goto _start;
}
case 10:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_72; 
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
lean_dec(x_1);
x_72 = lean_nat_dec_lt(x_2, x_66);
if (x_72 == 0)
{
lean_dec(x_66);
x_68 = x_2;
goto block_71;
}
else
{
lean_dec(x_2);
x_68 = x_66;
goto block_71;
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody), 2, 0);
x_70 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(x_69, x_67, x_68);
lean_dec(x_67);
return x_70;
}
}
case 11:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_73, x_2);
lean_dec(x_2);
lean_dec(x_73);
return x_74;
}
case 12:
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_nat_dec_lt(x_2, x_75);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_75);
x_78 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_76, x_2);
lean_dec(x_76);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec(x_2);
x_79 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_76, x_75);
lean_dec(x_76);
return x_79;
}
}
case 13:
{
return x_2;
}
default: 
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 2);
lean_inc(x_81);
lean_dec(x_1);
x_3 = x_80;
x_4 = x_81;
x_5 = x_2;
goto block_9;
}
}
block_9:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
x_1 = x_4;
x_2 = x_3;
goto _start;
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
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(x_3, x_2);
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
x_8 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(x_7, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0___boxed), 2, 0);
lean_inc(x_1);
lean_inc(x_4);
x_5 = l_Lean_RBNode_findCore___redArg(x_4, x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___redArg(x_4, x_3, x_1, x_6);
return x_7;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_1);
x_5 = l_Lean_RBNode_findCore___redArg(x_4, x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___redArg(x_4, x_3, x_1, x_6);
return x_7;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_1);
x_5 = l_Lean_RBNode_findCore___redArg(x_4, x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___redArg(x_4, x_3, x_1, x_6);
return x_7;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___redArg(x_5, x_3, x_1, x_6);
x_8 = lean_apply_2(x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___redArg(x_5, x_3, x_1, x_6);
x_8 = lean_apply_2(x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___redArg(x_5, x_3, x_1, x_6);
x_8 = lean_apply_2(x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
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
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__0(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_FreeIndices_insertParams(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_apply_2(x_1, x_3, x_4);
x_7 = lean_apply_3(x_2, x_5, x_3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_FreeIndices_instAndThenCollector() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_instAndThenCollector___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_3);
return x_4;
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
x_5 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_9 = lean_apply_3(x_1, x_8, x_2, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_9;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(x_2, x_3, x_1, x_9, x_10, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0;
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_4 = x_18;
x_5 = x_2;
x_6 = x_3;
goto block_10;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_box(0);
x_23 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_19, x_22);
x_24 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_20, x_2, x_23);
lean_dec(x_20);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_19);
x_25 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_20, x_2, x_3);
lean_dec(x_20);
return x_25;
}
}
case 3:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_4 = x_26;
x_5 = x_2;
x_6 = x_3;
goto block_10;
}
case 4:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_4 = x_27;
x_5 = x_2;
x_6 = x_3;
goto block_10;
}
case 5:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_28);
lean_dec(x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_28, x_30);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_box(0);
x_36 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_32, x_35);
x_37 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_33, x_2, x_36);
lean_dec(x_33);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_32);
x_38 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_33, x_2, x_3);
lean_dec(x_33);
return x_38;
}
}
case 9:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_39);
lean_dec(x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_39, x_41);
return x_42;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
return x_3;
}
}
case 10:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_11 = x_43;
x_12 = x_2;
x_13 = x_3;
goto block_17;
}
case 11:
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
case 12:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_11 = x_44;
x_12 = x_2;
x_13 = x_3;
goto block_17;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_45, x_2, x_3);
lean_dec(x_45);
return x_46;
}
}
block_10:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_5, x_4);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_6, x_4, x_8);
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
return x_6;
}
}
block_17:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_12, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_13, x_11, x_15);
return x_16;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_3(x_1, x_7, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_2);
x_17 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(x_15, x_2, x_3);
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_2, x_14, x_18);
x_1 = x_16;
x_2 = x_19;
x_3 = x_17;
goto _start;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_2);
x_25 = l_Lean_IR_FreeIndices_insertParams(x_2, x_22);
lean_dec(x_22);
x_26 = l_Lean_IR_FreeIndices_collectFnBody(x_23, x_25, x_3);
x_27 = lean_box(0);
x_28 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_2, x_21, x_27);
x_1 = x_24;
x_2 = x_28;
x_3 = x_26;
goto _start;
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec(x_1);
x_37 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_30, x_38);
x_33 = x_39;
goto block_36;
}
else
{
lean_dec(x_37);
lean_dec(x_30);
x_33 = x_3;
goto block_36;
}
block_36:
{
lean_object* x_34; 
x_34 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_31, x_2, x_33);
x_1 = x_32;
x_3 = x_34;
goto _start;
}
}
case 3:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_40, x_43);
x_1 = x_41;
x_3 = x_44;
goto _start;
}
else
{
lean_dec(x_42);
lean_dec(x_40);
x_1 = x_41;
goto _start;
}
}
case 4:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_57; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_49);
lean_dec(x_1);
x_57 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_47);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_47, x_58);
x_50 = x_59;
goto block_56;
}
else
{
lean_dec(x_57);
lean_dec(x_47);
x_50 = x_3;
goto block_56;
}
block_56:
{
lean_object* x_51; 
x_51 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_50, x_48, x_52);
x_1 = x_49;
x_3 = x_53;
goto _start;
}
else
{
lean_dec(x_51);
lean_dec(x_48);
x_1 = x_49;
x_3 = x_50;
goto _start;
}
}
}
case 5:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_70; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 5);
lean_inc(x_62);
lean_dec(x_1);
x_70 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_60);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
x_72 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_60, x_71);
x_63 = x_72;
goto block_69;
}
else
{
lean_dec(x_70);
lean_dec(x_60);
x_63 = x_3;
goto block_69;
}
block_69:
{
lean_object* x_64; 
x_64 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_box(0);
x_66 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_63, x_61, x_65);
x_1 = x_62;
x_3 = x_66;
goto _start;
}
else
{
lean_dec(x_64);
lean_dec(x_61);
x_1 = x_62;
x_3 = x_63;
goto _start;
}
}
}
case 8:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_75 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_box(0);
x_77 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_73, x_76);
x_1 = x_74;
x_3 = x_77;
goto _start;
}
else
{
lean_dec(x_75);
lean_dec(x_73);
x_1 = x_74;
goto _start;
}
}
case 9:
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_1, 1);
lean_inc(x_80);
lean_dec(x_1);
x_1 = x_80;
goto _start;
}
case 10:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; 
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 3);
lean_inc(x_83);
lean_dec(x_1);
x_88 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_82);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_box(0);
x_90 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_82, x_89);
x_84 = x_90;
goto block_87;
}
else
{
lean_dec(x_88);
lean_dec(x_82);
x_84 = x_3;
goto block_87;
}
block_87:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody), 3, 0);
x_86 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(x_85, x_83, x_2, x_84);
lean_dec(x_83);
return x_86;
}
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_91, x_2, x_3);
lean_dec(x_2);
return x_92;
}
case 12:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
lean_dec(x_1);
x_95 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_2, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_box(0);
x_97 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_3, x_93, x_96);
x_98 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_94, x_2, x_97);
lean_dec(x_94);
return x_98;
}
else
{
lean_object* x_99; 
lean_dec(x_95);
lean_dec(x_93);
x_99 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_94, x_2, x_3);
lean_dec(x_94);
return x_99;
}
}
case 13:
{
lean_dec(x_2);
return x_3;
}
default: 
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 2);
lean_inc(x_101);
lean_dec(x_1);
x_4 = x_100;
x_5 = x_101;
x_6 = x_2;
x_7 = x_3;
goto block_13;
}
}
block_13:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_6, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_7, x_4, x_9);
x_1 = x_5;
x_2 = x_6;
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
x_1 = x_5;
x_2 = x_6;
x_3 = x_7;
goto _start;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
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
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0(x_1, x_2, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0(x_1, x_2, x_5, x_6);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
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
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0(x_1, x_2, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0(x_1, x_2, x_5, x_6);
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
return x_7;
}
}
case 5:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_dec_eq(x_1, x_9);
return x_10;
}
case 6:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_IR_HasIndex_visitArgs(x_1, x_11);
return x_12;
}
case 7:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_Lean_IR_HasIndex_visitArgs(x_1, x_13);
return x_14;
}
case 8:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_nat_dec_eq(x_1, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_IR_HasIndex_visitArgs(x_1, x_16);
return x_18;
}
else
{
return x_17;
}
}
case 10:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_nat_dec_eq(x_1, x_19);
return x_20;
}
case 11:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
case 12:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_nat_dec_eq(x_1, x_23);
return x_24;
}
default: 
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_nat_dec_eq(x_1, x_25);
return x_26;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_13; 
x_6 = lean_box(1);
x_13 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_14);
lean_dec(x_14);
x_7 = x_15;
goto block_12;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_16);
lean_dec(x_16);
x_7 = x_17;
goto block_12;
}
block_12:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = l_Lean_IR_HasIndex_visitExpr(x_1, x_8);
if (x_10 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
return x_10;
}
}
case 1:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
return x_14;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_22; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_22 = lean_nat_dec_eq(x_1, x_16);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_IR_HasIndex_visitArg(x_1, x_17);
x_19 = x_23;
goto block_21;
}
else
{
x_19 = x_22;
goto block_21;
}
block_21:
{
if (x_19 == 0)
{
x_2 = x_18;
goto _start;
}
else
{
return x_19;
}
}
}
case 3:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_nat_dec_eq(x_1, x_24);
if (x_26 == 0)
{
x_2 = x_25;
goto _start;
}
else
{
return x_26;
}
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
x_34 = lean_nat_dec_eq(x_1, x_28);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = lean_nat_dec_eq(x_1, x_29);
x_31 = x_35;
goto block_33;
}
else
{
x_31 = x_34;
goto block_33;
}
block_33:
{
if (x_31 == 0)
{
x_2 = x_30;
goto _start;
}
else
{
return x_31;
}
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_ctor_get(x_2, 5);
x_42 = lean_nat_dec_eq(x_1, x_36);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_1, x_37);
x_39 = x_43;
goto block_41;
}
else
{
x_39 = x_42;
goto block_41;
}
block_41:
{
if (x_39 == 0)
{
x_2 = x_38;
goto _start;
}
else
{
return x_39;
}
}
}
case 8:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_nat_dec_eq(x_1, x_44);
if (x_46 == 0)
{
x_2 = x_45;
goto _start;
}
else
{
return x_46;
}
}
case 9:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 1);
x_2 = x_48;
goto _start;
}
case 10:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_ctor_get(x_2, 3);
x_52 = lean_nat_dec_eq(x_1, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_51);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_55 == 0)
{
lean_dec(x_54);
return x_52;
}
else
{
if (x_55 == 0)
{
lean_dec(x_54);
return x_52;
}
else
{
size_t x_56; size_t x_57; uint8_t x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_58 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0(x_1, x_51, x_56, x_57);
return x_58;
}
}
}
else
{
return x_52;
}
}
case 11:
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = l_Lean_IR_HasIndex_visitArg(x_1, x_59);
return x_60;
}
case 12:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
x_63 = lean_nat_dec_eq(x_1, x_61);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_IR_HasIndex_visitArgs(x_1, x_62);
return x_64;
}
else
{
return x_63;
}
}
case 13:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_box(0);
x_66 = lean_unbox(x_65);
return x_66;
}
default: 
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 2);
x_3 = x_67;
x_4 = x_68;
goto block_7;
}
}
block_7:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0(x_1, x_2, x_5, x_6);
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
lean_dec(x_2);
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
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_MaxIndex_instAndThenCollector = _init_l_Lean_IR_MaxIndex_instAndThenCollector();
lean_mark_persistent(l_Lean_IR_MaxIndex_instAndThenCollector);
l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0 = _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0);
l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0 = _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0);
l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0 = _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0);
l_Lean_IR_FreeIndices_instAndThenCollector = _init_l_Lean_IR_FreeIndices_instAndThenCollector();
lean_mark_persistent(l_Lean_IR_FreeIndices_instAndThenCollector);
l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0 = _init_l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
