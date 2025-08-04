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
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Expr_hasFreeVar(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__17(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_hasFreeVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector___private__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Arg_hasFreeVar(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_seq(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collect___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitParams_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitFnBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitArgs_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_seq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__4(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_skip___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_skip(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_hasFreeVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_HasIndex_visitVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__18___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector___private__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_instAndThenCollector___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_1, x_2, x_3);
return x_4;
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
lean_inc_ref(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArray(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1(lean_object* x_1, lean_object* x_2) {
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
lean_dec_ref(x_1);
x_3 = x_11;
x_4 = x_2;
goto block_6;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0___boxed), 3, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_15, x_14, x_2);
return x_16;
}
case 3:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_3 = x_17;
x_4 = x_2;
goto block_6;
}
case 4:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec_ref(x_1);
x_3 = x_18;
x_4 = x_2;
goto block_6;
}
case 5:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec_ref(x_1);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0___boxed), 3, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_21);
x_25 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_24, x_23, x_2);
return x_25;
}
case 9:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_7 = x_28;
x_8 = x_2;
goto block_10;
}
case 11:
{
lean_dec_ref(x_1);
return x_2;
}
case 12:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec_ref(x_1);
x_7 = x_29;
x_8 = x_2;
goto block_10;
}
default: 
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_30, x_2);
lean_dec_ref(x_30);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
lean_dec_ref(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectExpr), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_5, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_5, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_5, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_5, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__13(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody), 2, 0);
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectAlts(x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArgs(x_1, x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__3___boxed), 4, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_15, 0, x_10);
x_16 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_15, x_14, x_2);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__6___boxed), 4, 2);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__5___boxed), 4, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__7___boxed), 2, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_24, x_23, x_2);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec_ref(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__9___boxed), 4, 2);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_31, 0, x_26);
x_32 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_31, x_30, x_2);
return x_32;
}
case 3:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
lean_dec_ref(x_1);
x_35 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_36, 0, x_33);
x_37 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_36, x_35, x_2);
return x_37;
}
case 4:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
lean_dec_ref(x_1);
x_41 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__13___boxed), 2, 1);
lean_closure_set(x_42, 0, x_39);
x_43 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__8___boxed), 4, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_44, 0, x_38);
x_45 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_44, x_43, x_2);
return x_45;
}
case 5:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 5);
lean_inc(x_48);
lean_dec_ref(x_1);
x_49 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__13___boxed), 2, 1);
lean_closure_set(x_50, 0, x_47);
x_51 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__8___boxed), 4, 2);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_49);
x_52 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_52, 0, x_46);
x_53 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_52, x_51, x_2);
return x_53;
}
case 8:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec_ref(x_1);
x_56 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed), 3, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_57, 0, x_54);
x_58 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_57, x_56, x_2);
return x_58;
}
case 9:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_60);
lean_dec_ref(x_1);
x_61 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__18___boxed), 3, 1);
lean_closure_set(x_61, 0, x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed), 2, 1);
lean_closure_set(x_62, 0, x_59);
x_63 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_62, x_61, x_2);
return x_63;
}
case 10:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec_ref(x_1);
x_65 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectArg(x_64, x_2);
lean_dec(x_2);
lean_dec(x_64);
return x_65;
}
case 11:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__11___boxed), 3, 1);
lean_closure_set(x_68, 0, x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__7___boxed), 2, 1);
lean_closure_set(x_69, 0, x_66);
x_70 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_69, x_68, x_2);
return x_70;
}
case 12:
{
return x_2;
}
default: 
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
lean_dec(x_1);
x_3 = x_71;
x_4 = x_72;
x_5 = x_2;
goto block_9;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectFnBody___lam__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_7, x_6, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody___lam__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MaxIndex_collectFnBody___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody___lam__2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_MaxIndex_collectFnBody___lam__3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MaxIndex_collectFnBody___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_MaxIndex_collectFnBody___lam__6(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_MaxIndex_collectFnBody___lam__5(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MaxIndex_collectFnBody___lam__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_MaxIndex_collectFnBody___lam__9(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MaxIndex_collectFnBody___lam__13(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_MaxIndex_collectFnBody___lam__8(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody___lam__18(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectFnBody___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody___lam__11(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectFnBody(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_MaxIndex_collectDecl___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams___boxed), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = l_Lean_IR_MaxIndex_instAndThenCollector___private__1(x_6, x_5, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_MaxIndex_collectParams(x_8, x_2);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MaxIndex_collectDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_MaxIndex_collectDecl___lam__0(x_1, x_2, x_3);
return x_4;
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
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___lam__0___boxed), 2, 0);
lean_inc(x_1);
lean_inc_ref(x_4);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_1);
lean_inc_ref(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_4, x_1, x_7, x_3);
return x_8;
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec_ref(x_4);
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
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_4, x_1, x_7, x_3);
return x_8;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_4, x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_4, x_1, x_7, x_3);
return x_8;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_5, x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_5, x_1, x_7, x_3);
x_9 = lean_apply_2(x_2, x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_5, x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_5, x_1, x_7, x_3);
x_9 = lean_apply_2(x_2, x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_withJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectVar___closed__0;
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___redArg(x_5, x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_5, x_1, x_7, x_3);
x_9 = lean_apply_2(x_2, x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_nat_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_nat_dec_lt(x_1, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_1, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_2, x_8);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_24 = lean_nat_add(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; 
lean_dec(x_27);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
x_37 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_38 = lean_nat_add(x_37, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_add(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_31);
lean_ctor_set(x_43, 4, x_19);
if (lean_is_scalar(x_26)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_26;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_37, x_46);
lean_dec(x_46);
lean_dec(x_37);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
lean_ctor_set(x_48, 2, x_6);
lean_ctor_set(x_48, 3, x_7);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_13, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_39 = x_49;
x_40 = x_48;
x_41 = x_50;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_39 = x_49;
x_40 = x_48;
x_41 = x_51;
goto block_45;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
x_55 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_56 = lean_nat_add(x_55, x_15);
lean_dec(x_15);
x_57 = lean_nat_add(x_55, x_27);
lean_dec(x_27);
lean_dec(x_55);
lean_inc_ref(x_7);
if (lean_is_scalar(x_26)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_26;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_7);
lean_ctor_set(x_58, 4, x_18);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_7, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_7, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_7, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 0);
lean_dec(x_64);
lean_ctor_set(x_7, 4, x_19);
lean_ctor_set(x_7, 3, x_58);
lean_ctor_set(x_7, 2, x_17);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_56);
return x_7;
}
else
{
lean_object* x_65; 
lean_dec(x_7);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_16);
lean_ctor_set(x_65, 2, x_17);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_19);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_12, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_12);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_12, 4);
x_69 = lean_ctor_get(x_12, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_12, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_66, 1);
x_73 = lean_ctor_get(x_66, 2);
x_74 = lean_ctor_get(x_66, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
lean_ctor_set(x_66, 4, x_68);
lean_ctor_set(x_66, 3, x_68);
lean_ctor_set(x_66, 2, x_6);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 0, x_13);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_9;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_66);
lean_ctor_set(x_78, 4, x_12);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_66, 1);
x_80 = lean_ctor_get(x_66, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_13);
lean_ctor_set(x_82, 1, x_5);
lean_ctor_set(x_82, 2, x_6);
lean_ctor_set(x_82, 3, x_68);
lean_ctor_set(x_82, 4, x_68);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_83 = lean_alloc_ctor(0, 5, 0);
} else {
 x_83 = x_9;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_12);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_12, 4);
x_85 = lean_ctor_get(x_12, 1);
x_86 = lean_ctor_get(x_12, 2);
lean_inc(x_84);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_12);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_66, 2);
lean_inc(x_88);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_89 = x_66;
} else {
 lean_dec_ref(x_66);
 x_89 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(3u);
lean_inc_n(x_84, 2);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set(x_91, 2, x_6);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_84);
lean_inc(x_84);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_84);
lean_ctor_set(x_92, 4, x_84);
if (lean_is_scalar(x_9)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_9;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_92);
return x_93;
}
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_12, 4);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_12, 1);
x_97 = lean_ctor_get(x_12, 2);
x_98 = lean_ctor_get(x_12, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_12, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 0);
lean_dec(x_100);
x_101 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_12, 4, x_66);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_9;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_102, 2, x_97);
lean_ctor_set(x_102, 3, x_12);
lean_ctor_set(x_102, 4, x_94);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_12, 1);
x_104 = lean_ctor_get(x_12, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_13);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 3, x_66);
lean_ctor_set(x_106, 4, x_66);
if (lean_is_scalar(x_9)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_9;
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_106);
lean_ctor_set(x_107, 4, x_94);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_94);
lean_ctor_set(x_109, 4, x_12);
return x_109;
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_1);
lean_ctor_set(x_110, 2, x_2);
lean_ctor_set(x_110, 3, x_7);
lean_ctor_set(x_110, 4, x_8);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
x_111 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_2, x_7);
x_112 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_ctor_get(x_8, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 4);
lean_inc(x_118);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_mul(x_119, x_113);
x_121 = lean_nat_dec_lt(x_120, x_114);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
x_122 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_123 = lean_nat_add(x_122, x_113);
lean_dec(x_113);
lean_dec(x_122);
if (lean_is_scalar(x_9)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_9;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_ctor_set(x_124, 2, x_6);
lean_ctor_set(x_124, 3, x_111);
lean_ctor_set(x_124, 4, x_8);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_125 = x_111;
} else {
 lean_dec_ref(x_111);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_118, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_118, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_118, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_118, 4);
lean_inc(x_131);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_nat_mul(x_132, x_126);
x_134 = lean_nat_dec_lt(x_127, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_145; lean_object* x_146; 
lean_dec(x_127);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_135 = x_118;
} else {
 lean_dec_ref(x_118);
 x_135 = lean_box(0);
}
x_136 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_137 = lean_nat_add(x_136, x_113);
lean_dec(x_136);
x_145 = lean_nat_add(x_112, x_126);
lean_dec(x_126);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_130, 0);
lean_inc(x_153);
x_146 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_146 = x_154;
goto block_152;
}
block_144:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_nat_add(x_139, x_140);
lean_dec(x_140);
lean_dec(x_139);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_5);
lean_ctor_set(x_142, 2, x_6);
lean_ctor_set(x_142, 3, x_131);
lean_ctor_set(x_142, 4, x_8);
if (lean_is_scalar(x_125)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_125;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_128);
lean_ctor_set(x_143, 2, x_129);
lean_ctor_set(x_143, 3, x_138);
lean_ctor_set(x_143, 4, x_142);
return x_143;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_nat_add(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (lean_is_scalar(x_9)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_9;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set(x_148, 2, x_116);
lean_ctor_set(x_148, 3, x_117);
lean_ctor_set(x_148, 4, x_130);
x_149 = lean_nat_add(x_112, x_113);
lean_dec(x_113);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
x_138 = x_148;
x_139 = x_149;
x_140 = x_150;
goto block_144;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_138 = x_148;
x_139 = x_149;
x_140 = x_151;
goto block_144;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_9);
x_155 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_156 = lean_nat_add(x_155, x_113);
lean_dec(x_155);
x_157 = lean_nat_add(x_112, x_113);
lean_dec(x_113);
x_158 = lean_nat_add(x_157, x_127);
lean_dec(x_127);
lean_dec(x_157);
lean_inc_ref(x_8);
if (lean_is_scalar(x_125)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_125;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_5);
lean_ctor_set(x_159, 2, x_6);
lean_ctor_set(x_159, 3, x_118);
lean_ctor_set(x_159, 4, x_8);
x_160 = !lean_is_exclusive(x_8);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_8, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_8, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_8, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_8, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_8, 0);
lean_dec(x_165);
lean_ctor_set(x_8, 4, x_159);
lean_ctor_set(x_8, 3, x_117);
lean_ctor_set(x_8, 2, x_116);
lean_ctor_set(x_8, 1, x_115);
lean_ctor_set(x_8, 0, x_156);
return x_8;
}
else
{
lean_object* x_166; 
lean_dec(x_8);
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_115);
lean_ctor_set(x_166, 2, x_116);
lean_ctor_set(x_166, 3, x_117);
lean_ctor_set(x_166, 4, x_159);
return x_166;
}
}
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_111, 3);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_111);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_111, 4);
x_170 = lean_ctor_get(x_111, 1);
x_171 = lean_ctor_get(x_111, 2);
x_172 = lean_ctor_get(x_111, 3);
lean_dec(x_172);
x_173 = lean_ctor_get(x_111, 0);
lean_dec(x_173);
x_174 = lean_unsigned_to_nat(3u);
lean_inc(x_169);
lean_ctor_set(x_111, 3, x_169);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_175 = x_9;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_167);
lean_ctor_set(x_175, 4, x_111);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_111, 4);
x_177 = lean_ctor_get(x_111, 1);
x_178 = lean_ctor_get(x_111, 2);
lean_inc(x_176);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_111);
x_179 = lean_unsigned_to_nat(3u);
lean_inc(x_176);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_112);
lean_ctor_set(x_180, 1, x_5);
lean_ctor_set(x_180, 2, x_6);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set(x_180, 4, x_176);
if (lean_is_scalar(x_9)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_9;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_167);
lean_ctor_set(x_181, 4, x_180);
return x_181;
}
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_111, 4);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_111);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_184 = lean_ctor_get(x_111, 1);
x_185 = lean_ctor_get(x_111, 2);
x_186 = lean_ctor_get(x_111, 4);
lean_dec(x_186);
x_187 = lean_ctor_get(x_111, 3);
lean_dec(x_187);
x_188 = lean_ctor_get(x_111, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_182, 1);
x_191 = lean_ctor_get(x_182, 2);
x_192 = lean_ctor_get(x_182, 4);
lean_dec(x_192);
x_193 = lean_ctor_get(x_182, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_182, 0);
lean_dec(x_194);
x_195 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_182, 4, x_167);
lean_ctor_set(x_182, 3, x_167);
lean_ctor_set(x_182, 2, x_185);
lean_ctor_set(x_182, 1, x_184);
lean_ctor_set(x_182, 0, x_112);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_9;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 3, x_182);
lean_ctor_set(x_196, 4, x_111);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_182, 1);
x_198 = lean_ctor_get(x_182, 2);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_182);
x_199 = lean_unsigned_to_nat(3u);
x_200 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_200, 0, x_112);
lean_ctor_set(x_200, 1, x_184);
lean_ctor_set(x_200, 2, x_185);
lean_ctor_set(x_200, 3, x_167);
lean_ctor_set(x_200, 4, x_167);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_201 = lean_alloc_ctor(0, 5, 0);
} else {
 x_201 = x_9;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_197);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_111);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = lean_ctor_get(x_111, 1);
x_203 = lean_ctor_get(x_111, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_111);
x_204 = lean_ctor_get(x_182, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 2);
lean_inc(x_205);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 x_206 = x_182;
} else {
 lean_dec_ref(x_182);
 x_206 = lean_box(0);
}
x_207 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_112);
lean_ctor_set(x_208, 1, x_202);
lean_ctor_set(x_208, 2, x_203);
lean_ctor_set(x_208, 3, x_167);
lean_ctor_set(x_208, 4, x_167);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_112);
lean_ctor_set(x_209, 1, x_5);
lean_ctor_set(x_209, 2, x_6);
lean_ctor_set(x_209, 3, x_167);
lean_ctor_set(x_209, 4, x_167);
if (lean_is_scalar(x_9)) {
 x_210 = lean_alloc_ctor(0, 5, 0);
} else {
 x_210 = x_9;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_208);
lean_ctor_set(x_210, 4, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_212 = lean_alloc_ctor(0, 5, 0);
} else {
 x_212 = x_9;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_5);
lean_ctor_set(x_212, 2, x_6);
lean_ctor_set(x_212, 3, x_111);
lean_ctor_set(x_212, 4, x_182);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_1);
lean_ctor_set(x_214, 2, x_2);
lean_ctor_set(x_214, 3, x_3);
lean_ctor_set(x_214, 4, x_3);
return x_214;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_12, x_14, x_4);
x_5 = x_15;
goto block_9;
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_12, x_14, x_4);
x_5 = x_15;
goto block_9;
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2_spec__2(x_1, x_7, x_3, x_5);
return x_8;
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
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_FreeIndices_insertParams_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_insertParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_FreeIndices_insertParams(x_1, x_2);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector___private__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_instAndThenCollector___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_1, x_2, x_3, x_4);
return x_5;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_4, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_4, x_7, x_3);
return x_8;
}
else
{
lean_dec(x_4);
return x_3;
}
}
else
{
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
lean_inc_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArray(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_6, x_3);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
x_4 = x_20;
x_5 = x_2;
x_6 = x_3;
goto block_11;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0___boxed), 4, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1___boxed), 3, 1);
lean_closure_set(x_24, 0, x_21);
x_25 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_24, x_23, x_2, x_3);
return x_25;
}
case 3:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec_ref(x_1);
x_4 = x_26;
x_5 = x_2;
x_6 = x_3;
goto block_11;
}
case 4:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec_ref(x_1);
x_4 = x_27;
x_5 = x_2;
x_6 = x_3;
goto block_11;
}
case 5:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec_ref(x_1);
x_29 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_28, x_2);
lean_dec(x_2);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_28, x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_28, x_31, x_3);
return x_32;
}
else
{
lean_dec(x_28);
return x_3;
}
}
else
{
lean_dec(x_28);
return x_3;
}
}
case 8:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_1);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0___boxed), 4, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1___boxed), 3, 1);
lean_closure_set(x_36, 0, x_33);
x_37 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_36, x_35, x_2, x_3);
return x_37;
}
case 9:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec_ref(x_1);
x_39 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_38, x_2);
lean_dec(x_2);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_38, x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_38, x_41, x_3);
return x_42;
}
else
{
lean_dec(x_38);
return x_3;
}
}
else
{
lean_dec(x_38);
return x_3;
}
}
case 10:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec_ref(x_1);
x_12 = x_43;
x_13 = x_2;
x_14 = x_3;
goto block_19;
}
case 11:
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
case 12:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec_ref(x_1);
x_12 = x_44;
x_13 = x_2;
x_14 = x_3;
goto block_19;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_1);
x_46 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_45, x_2, x_3);
lean_dec_ref(x_45);
return x_46;
}
}
block_11:
{
uint8_t x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_4, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_4, x_9, x_6);
return x_10;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_dec(x_4);
return x_6;
}
}
block_19:
{
uint8_t x_15; 
x_15 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_12, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_12, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_12, x_17, x_14);
return x_18;
}
else
{
lean_dec(x_12);
return x_14;
}
}
else
{
lean_dec(x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_dec_ref(x_2);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_6, x_3);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_7, x_4);
x_9 = l_Lean_IR_FreeIndices_collectFnBody(x_2, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_IR_FreeIndices_collectFnBody(x_2, x_4, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_FreeIndices_insertParams(x_3, x_1);
x_6 = l_Lean_IR_FreeIndices_collectFnBody(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_7, x_4);
x_9 = l_Lean_IR_FreeIndices_collectFnBody(x_2, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_IR_FreeIndices_collectFnBody(x_2, x_4, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_6, x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_6, x_3);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_6, x_3);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody), 3, 0);
x_6 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectAlts(x_5, x_1, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArgs(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_FreeIndices_insertParams_spec__0___redArg(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_FreeIndices_insertParams_spec__1___redArg(x_1, x_6, x_3);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__2___boxed), 5, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectExpr), 3, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_16, x_15, x_2, x_3);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__3___boxed), 4, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__4___boxed), 5, 2);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_21);
x_24 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_22, x_23, x_2, x_3);
return x_24;
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec_ref(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed), 4, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__6___boxed), 5, 2);
lean_closure_set(x_29, 0, x_26);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed), 3, 1);
lean_closure_set(x_30, 0, x_25);
x_31 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_30, x_29, x_2, x_3);
return x_31;
}
case 3:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed), 4, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed), 3, 1);
lean_closure_set(x_35, 0, x_32);
x_36 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_35, x_34, x_2, x_3);
return x_36;
}
case 4:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
lean_dec_ref(x_1);
x_40 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed), 4, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__11___boxed), 3, 1);
lean_closure_set(x_41, 0, x_38);
x_42 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__8___boxed), 5, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_40);
x_43 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed), 3, 1);
lean_closure_set(x_43, 0, x_37);
x_44 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_43, x_42, x_2, x_3);
return x_44;
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 5);
lean_inc(x_47);
lean_dec_ref(x_1);
x_48 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed), 4, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__11___boxed), 3, 1);
lean_closure_set(x_49, 0, x_46);
x_50 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__8___boxed), 5, 2);
lean_closure_set(x_50, 0, x_49);
lean_closure_set(x_50, 1, x_48);
x_51 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed), 3, 1);
lean_closure_set(x_51, 0, x_45);
x_52 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_51, x_50, x_2, x_3);
return x_52;
}
case 8:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec_ref(x_1);
x_55 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed), 4, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed), 3, 1);
lean_closure_set(x_56, 0, x_53);
x_57 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_56, x_55, x_2, x_3);
return x_57;
}
case 9:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_59);
lean_dec_ref(x_1);
x_60 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__17___boxed), 4, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed), 3, 1);
lean_closure_set(x_61, 0, x_58);
x_62 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_61, x_60, x_2, x_3);
return x_62;
}
case 10:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec_ref(x_1);
x_64 = l___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg(x_63, x_2, x_3);
lean_dec(x_2);
return x_64;
}
case 11:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_66);
lean_dec_ref(x_1);
x_67 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__10___boxed), 4, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__9___boxed), 3, 1);
lean_closure_set(x_68, 0, x_65);
x_69 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_68, x_67, x_2, x_3);
return x_69;
}
case 12:
{
lean_dec(x_2);
return x_3;
}
default: 
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
lean_dec(x_1);
x_4 = x_70;
x_5 = x_71;
x_6 = x_2;
x_7 = x_3;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__0___boxed), 4, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_IR_FreeIndices_collectFnBody___lam__1___boxed), 3, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = l_Lean_IR_FreeIndices_instAndThenCollector___private__1(x_9, x_8, x_6, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody___lam__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FreeIndices_collectFnBody___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_FreeIndices_collectFnBody___lam__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody___lam__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_FreeIndices_collectFnBody___lam__4(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody___lam__5(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_FreeIndices_collectFnBody___lam__6(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FreeIndices_collectFnBody___lam__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FreeIndices_collectFnBody___lam__11(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_FreeIndices_collectFnBody___lam__8(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody___lam__17(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_FreeIndices_collectFnBody___lam__10(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FreeIndices_collectFnBody___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FreeIndices_collectFnBody___lam__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = l_Lean_IR_FreeIndices_collectFnBody(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_freeIndices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
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
uint8_t x_11; 
x_11 = 0;
return x_11;
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_6);
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
uint8_t x_12; 
x_12 = 0;
return x_12;
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
uint8_t x_21; 
x_21 = 0;
return x_21;
}
case 12:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_nat_dec_eq(x_1, x_22);
return x_23;
}
default: 
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_nat_dec_eq(x_1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_HasIndex_visitExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_HasIndex_visitExpr(x_1, x_2);
lean_dec_ref(x_2);
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
uint8_t x_6; uint8_t x_7; lean_object* x_12; 
x_6 = 1;
x_12 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_13);
lean_dec(x_13);
x_7 = x_14;
goto block_11;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_15);
lean_dec(x_15);
x_7 = x_16;
goto block_11;
}
block_11:
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
return x_6;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
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
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get(x_2, 3);
x_50 = lean_nat_dec_eq(x_1, x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_49);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
lean_dec(x_52);
return x_50;
}
else
{
if (x_53 == 0)
{
lean_dec(x_52);
return x_50;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_56 = l_Array_anyMUnsafe_any___at___Lean_IR_HasIndex_visitFnBody_spec__0(x_1, x_49, x_54, x_55);
return x_56;
}
}
}
else
{
return x_50;
}
}
case 10:
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = l_Lean_IR_HasIndex_visitArg(x_1, x_57);
return x_58;
}
case 11:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_nat_dec_eq(x_1, x_59);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_IR_HasIndex_visitArgs(x_1, x_60);
return x_62;
}
else
{
return x_61;
}
}
case 12:
{
uint8_t x_63; 
x_63 = 0;
return x_63;
}
default: 
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 2);
x_3 = x_64;
x_4 = x_65;
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
