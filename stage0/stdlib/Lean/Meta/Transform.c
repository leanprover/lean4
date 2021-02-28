// Lean compiler output
// Module: Lean.Meta.Transform
// Imports: Init Lean.Meta.Basic
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
lean_object* l_Lean_Meta_transform_visit_visitLambda_match__1(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__2___boxed(lean_object**);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_transform_visit_visitLambda(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6(lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___at_Lean_Core_betaReduce___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2(lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_run___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_betaReduce___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall_match__1(lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce_match__3(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___closed__1;
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost_match__1(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5(lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6(lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce_match__1(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1;
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5___boxed__const__1;
extern lean_object* l_Lean_Expr_updateProj_x21___closed__3;
lean_object* l_Lean_Core_transform_visit(lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Meta_transform_visit_visitPost(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1(lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_run_x27___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2;
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1(lean_object*);
lean_object* l_Lean_Meta_zetaReduce_match__2(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Core_transform_visit_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1;
lean_object* l_Lean_Meta_transform_visit_visitLet_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_betaReduce___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8(lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall(lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__1___boxed(lean_object**);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Meta_transform_visit_visitPost___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___at_Lean_Core_betaReduce___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___boxed(lean_object*);
lean_object* l_Lean_Meta_zetaReduce_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOfReaderT___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1;
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2(lean_object*);
lean_object* l_Lean_Core_transform___rarg___closed__1;
lean_object* l_Lean_Core_transform_visit_visitPost_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Core_transform_visit_visitPost_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit_visitPost_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Core_transform_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_5, x_9, x_10, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_3, x_14, x_15, x_16, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_2, x_20, x_21, x_22, x_24);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
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
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_5(x_4, x_26, x_27, x_28, x_29, x_31);
return x_32;
}
case 10:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_6, x_33, x_34, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_7, x_38, x_39, x_40, x_42);
return x_43;
}
default: 
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_apply_1(x_8, x_1);
return x_44;
}
}
}
}
lean_object* l_Lean_Core_transform_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 1;
x_13 = x_1 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_2, x_1, x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_15, x_10);
return x_16;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_8 < x_7;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_9;
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_array_uget(x_9, x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_9, x_8, x_17);
x_19 = x_16;
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_19, x_10);
x_22 = lean_box_usize(x_8);
x_23 = lean_box_usize(x_7);
x_24 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1___boxed), 11, 10);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_18);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_2);
lean_closure_set(x_24, 4, x_3);
lean_closure_set(x_24, 5, x_4);
lean_closure_set(x_24, 6, x_5);
lean_closure_set(x_24, 7, x_6);
lean_closure_set(x_24, 8, x_23);
lean_closure_set(x_24, 9, x_10);
x_25 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_mkAppN(x_1, x_9);
x_11 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = x_1;
x_14 = lean_box_usize(x_12);
x_15 = l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___boxed), 10, 9);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_6);
lean_closure_set(x_16, 5, x_7);
lean_closure_set(x_16, 6, x_14);
lean_closure_set(x_16, 7, x_15);
lean_closure_set(x_16, 8, x_13);
x_17 = x_16;
lean_inc(x_8);
x_18 = lean_apply_1(x_17, x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_8);
x_20 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_array_set(x_9, x_10, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_10, x_15);
lean_dec(x_10);
x_8 = x_12;
x_9 = x_14;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_11);
lean_inc(x_7);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2), 10, 9);
lean_closure_set(x_19, 0, x_9);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
lean_closure_set(x_19, 7, x_11);
lean_closure_set(x_19, 8, x_7);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg), 11, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOfReaderT___rarg___lambda__2), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___rarg), 6, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_13 = (uint8_t)((x_12 << 24) >> 61);
x_14 = lean_expr_update_lambda(x_1, x_13, x_9, x_10);
x_15 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_19);
x_21 = (uint8_t)((x_19 << 24) >> 61);
x_22 = lean_expr_update_lambda(x_20, x_21, x_9, x_10);
x_23 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_8);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_24 = l_Lean_instInhabitedExpr;
x_25 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_26 = lean_panic_fn(x_24, x_25);
x_27 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_8);
return x_27;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1), 10, 9);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_8);
lean_closure_set(x_13, 8, x_11);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_13 = (uint8_t)((x_12 << 24) >> 61);
x_14 = lean_expr_update_forall(x_1, x_13, x_9, x_10);
x_15 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_19);
x_21 = (uint8_t)((x_19 << 24) >> 61);
x_22 = lean_expr_update_forall(x_20, x_21, x_9, x_10);
x_23 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_8);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_24 = l_Lean_instInhabitedExpr;
x_25 = l_Lean_Expr_updateForallE_x21___closed__2;
x_26 = lean_panic_fn(x_24, x_25);
x_27 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_8);
return x_27;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3), 10, 9);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_8);
lean_closure_set(x_13, 8, x_11);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_expr_update_let(x_1, x_9, x_10, x_11);
x_14 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_20 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_uint64(x_20, sizeof(void*)*4, x_19);
x_21 = lean_expr_update_let(x_20, x_9, x_10, x_11);
x_22 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_8);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_23 = l_Lean_instInhabitedExpr;
x_24 = l_Lean_Expr_updateLet_x21___closed__2;
x_25 = lean_panic_fn(x_23, x_24);
x_26 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_25, x_8);
return x_26;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__5), 11, 10);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_10);
lean_closure_set(x_14, 9, x_12);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__6), 12, 11);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_9);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_10);
lean_closure_set(x_14, 9, x_12);
lean_closure_set(x_14, 10, x_11);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_update_mdata(x_1, x_9);
x_12 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint64(x_16, sizeof(void*)*2, x_15);
x_17 = lean_expr_update_mdata(x_16, x_9);
x_18 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_8);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_1);
x_19 = l_Lean_instInhabitedExpr;
x_20 = l_Lean_Expr_updateMData_x21___closed__3;
x_21 = lean_panic_fn(x_19, x_20);
x_22 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_8);
return x_22;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_update_proj(x_1, x_9);
x_12 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_17 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint64(x_17, sizeof(void*)*3, x_16);
x_18 = lean_expr_update_proj(x_17, x_9);
x_19 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_8);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_1);
x_20 = l_Lean_instInhabitedExpr;
x_21 = l_Lean_Expr_updateProj_x21___closed__3;
x_22 = lean_panic_fn(x_20, x_21);
x_23 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_8);
return x_23;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
switch (lean_obj_tag(x_14)) {
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_14, x_15);
x_17 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_14, x_18, x_20, x_7);
return x_21;
}
case 6:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_7);
lean_inc(x_8);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__2), 11, 10);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_23);
lean_closure_set(x_25, 7, x_7);
lean_closure_set(x_25, 8, x_14);
lean_closure_set(x_25, 9, x_8);
x_26 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 2);
lean_inc(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_27, x_7);
lean_inc(x_8);
x_30 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__4), 11, 10);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_5);
lean_closure_set(x_30, 5, x_6);
lean_closure_set(x_30, 6, x_28);
lean_closure_set(x_30, 7, x_7);
lean_closure_set(x_30, 8, x_14);
lean_closure_set(x_30, 9, x_8);
x_31 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 3);
lean_inc(x_34);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_32, x_7);
lean_inc(x_8);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__7), 12, 11);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_4);
lean_closure_set(x_36, 4, x_5);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_33);
lean_closure_set(x_36, 7, x_7);
lean_closure_set(x_36, 8, x_34);
lean_closure_set(x_36, 9, x_14);
lean_closure_set(x_36, 10, x_8);
x_37 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_35, x_36);
return x_37;
}
case 10:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_38, x_7);
x_40 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__8), 9, 8);
lean_closure_set(x_40, 0, x_14);
lean_closure_set(x_40, 1, x_1);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_3);
lean_closure_set(x_40, 4, x_4);
lean_closure_set(x_40, 5, x_5);
lean_closure_set(x_40, 6, x_6);
lean_closure_set(x_40, 7, x_7);
x_41 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_39, x_40);
return x_41;
}
case 11:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_14, 2);
lean_inc(x_42);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_42, x_7);
x_44 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__9), 9, 8);
lean_closure_set(x_44, 0, x_14);
lean_closure_set(x_44, 1, x_1);
lean_closure_set(x_44, 2, x_2);
lean_closure_set(x_44, 3, x_3);
lean_closure_set(x_44, 4, x_4);
lean_closure_set(x_44, 5, x_5);
lean_closure_set(x_44, 6, x_6);
lean_closure_set(x_44, 7, x_7);
x_45 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_43, x_44);
return x_45;
}
default: 
{
lean_object* x_46; 
lean_dec(x_8);
x_46 = l_Lean_Core_transform_visit_visitPost___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_7);
return x_46;
}
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
x_11 = lean_apply_1(x_3, x_7);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg___lambda__10), 9, 8);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
lean_closure_set(x_13, 6, x_10);
lean_closure_set(x_13, 7, x_8);
x_14 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_11, x_13);
return x_14;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_10);
x_13 = lean_apply_1(x_2, x_3);
x_14 = lean_apply_5(x_4, lean_box(0), x_13, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 4);
x_19 = lean_ctor_get(x_6, 5);
x_20 = lean_ctor_get(x_6, 6);
x_21 = lean_ctor_get(x_6, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_apply_1(x_2, x_3);
x_24 = lean_apply_5(x_4, lean_box(0), x_23, x_22, x_7, x_8);
return x_24;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__1(x_7, x_1, x_2, x_3, x_10, x_4, x_5, x_6);
lean_dec(x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_13 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_12, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
return x_4;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__2), 6, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_dec(x_19);
lean_ctor_set(x_13, 1, x_17);
lean_inc(x_2);
x_20 = l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10);
x_21 = lean_apply_5(x_11, lean_box(0), x_20, x_13, x_14, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 2);
x_24 = lean_ctor_get(x_13, 3);
x_25 = lean_ctor_get(x_13, 4);
x_26 = lean_ctor_get(x_13, 5);
x_27 = lean_ctor_get(x_13, 6);
x_28 = lean_ctor_get(x_13, 7);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 4, x_25);
lean_ctor_set(x_29, 5, x_26);
lean_ctor_set(x_29, 6, x_27);
lean_ctor_set(x_29, 7, x_28);
lean_inc(x_2);
x_30 = l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___at_Lean_Core_transform_visit___spec__4___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10);
x_31 = lean_apply_5(x_11, lean_box(0), x_30, x_29, x_14, x_15);
return x_31;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__1(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_11, x_12, x_13);
lean_dec(x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_20 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_19, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__2), 13, 9);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
lean_closure_set(x_15, 7, x_12);
lean_closure_set(x_15, 8, x_11);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_11 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_1, x_2, x_5, x_8);
lean_dec(x_5);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__8), 6, 5);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_6);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
return x_17;
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_8);
lean_inc(x_6);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
lean_inc(x_1);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_9);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
lean_inc(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__1), 10, 9);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_9);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Core_transform_visit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Core_transform_visit_visitPost___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_7);
return x_14;
}
}
}
lean_object* l_Lean_Core_transform_visit_visitPost___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
x_9 = lean_apply_1(x_4, x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit_visitPost___rarg___lambda__1), 8, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_8);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Core_transform_visit_visitPost(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit_visitPost___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_10, x_11);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___at_Lean_Core_transform_visit___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_mk_ref(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg___lambda__4___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_StateRefT_x27_run___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg___lambda__5), 5, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Core_transform___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg___lambda__3___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Core_transform___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg___lambda__2), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Core_transform___rarg___closed__1;
lean_inc(x_2);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
lean_inc(x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg___lambda__6), 10, 9);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_7);
lean_closure_set(x_12, 5, x_8);
lean_closure_set(x_12, 6, x_4);
lean_closure_set(x_12, 7, x_2);
lean_closure_set(x_12, 8, x_9);
lean_inc(x_9);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_StateRefT_x27_run_x27___rarg___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Core_transform(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_transform___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_transform___rarg___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_transform___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_transform___rarg___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_10 = lean_apply_4(x_2, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_betaReduce___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_6 < x_5;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_7;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_7, x_6, x_16);
x_18 = x_15;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_18, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_6 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_6, x_24);
x_6 = x_23;
x_7 = x_25;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_array_set(x_6, x_7, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_7, x_15);
lean_dec(x_7);
x_5 = x_12;
x_6 = x_14;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_6);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = x_6;
x_24 = lean_box_usize(x_22);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5___boxed__const__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Core_betaReduce___spec__4___boxed), 11, 7);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_3);
lean_closure_set(x_26, 3, x_4);
lean_closure_set(x_26, 4, x_24);
lean_closure_set(x_26, 5, x_25);
lean_closure_set(x_26, 6, x_23);
x_27 = x_26;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = lean_apply_4(x_27, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_mkAppN(x_19, x_29);
lean_dec(x_29);
x_32 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_31, x_8, x_9, x_10, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_5(x_2, x_8, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___rarg), 6, 0);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___at_Lean_Core_betaReduce___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
x_10 = lean_apply_4(x_1, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
switch (lean_obj_tag(x_18)) {
case 5:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux(x_18, x_20);
x_22 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_26 = l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5(x_1, x_2, x_3, x_4, x_18, x_23, x_25, x_6, x_7, x_8, x_19);
return x_26;
}
case 6:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_30, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_31);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_31, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = (uint8_t)((x_32 << 24) >> 61);
x_40 = lean_expr_update_lambda(x_18, x_39, x_34, x_37);
x_41 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_40, x_6, x_7, x_8, x_38);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_free_object(x_18);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_18);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
x_52 = lean_ctor_get(x_18, 2);
x_53 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_51);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_51, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_52);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_52, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_51);
lean_ctor_set(x_60, 2, x_52);
lean_ctor_set_uint64(x_60, sizeof(void*)*3, x_53);
x_61 = (uint8_t)((x_53 << 24) >> 61);
x_62 = lean_expr_update_lambda(x_60, x_61, x_55, x_58);
x_63 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_62, x_6, x_7, x_8, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_70 = x_54;
} else {
 lean_dec_ref(x_54);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
case 7:
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_10, 1);
lean_inc(x_72);
lean_dec(x_10);
x_73 = !lean_is_exclusive(x_18);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_18, 0);
x_75 = lean_ctor_get(x_18, 1);
x_76 = lean_ctor_get(x_18, 2);
x_77 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_75);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_78 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_75, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_76);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_81 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_76, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = (uint8_t)((x_77 << 24) >> 61);
x_85 = lean_expr_update_forall(x_18, x_84, x_79, x_82);
x_86 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_85, x_6, x_7, x_8, x_83);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_79);
lean_free_object(x_18);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
return x_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_free_object(x_18);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
return x_78;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_78, 0);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_78);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_18, 0);
x_96 = lean_ctor_get(x_18, 1);
x_97 = lean_ctor_get(x_18, 2);
x_98 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_96);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_96, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_97);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_102 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_97, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_96);
lean_ctor_set(x_105, 2, x_97);
lean_ctor_set_uint64(x_105, sizeof(void*)*3, x_98);
x_106 = (uint8_t)((x_98 << 24) >> 61);
x_107 = lean_expr_update_forall(x_105, x_106, x_100, x_103);
x_108 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_107, x_6, x_7, x_8, x_104);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_ctor_get(x_102, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_102, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_111 = x_102;
} else {
 lean_dec_ref(x_102);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_99, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_115 = x_99;
} else {
 lean_dec_ref(x_99);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
case 8:
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_10, 1);
lean_inc(x_117);
lean_dec(x_10);
x_118 = !lean_is_exclusive(x_18);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_18, 0);
x_120 = lean_ctor_get(x_18, 1);
x_121 = lean_ctor_get(x_18, 2);
x_122 = lean_ctor_get(x_18, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_120);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_123 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_120, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_121);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_126 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_121, x_6, x_7, x_8, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_122);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_129 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_122, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_expr_update_let(x_18, x_124, x_127, x_130);
x_133 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_132, x_6, x_7, x_8, x_131);
return x_133;
}
else
{
uint8_t x_134; 
lean_dec(x_127);
lean_dec(x_124);
lean_free_object(x_18);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_129);
if (x_134 == 0)
{
return x_129;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_129, 0);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_129);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_124);
lean_free_object(x_18);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_126);
if (x_138 == 0)
{
return x_126;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_126, 0);
x_140 = lean_ctor_get(x_126, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_126);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_free_object(x_18);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_123);
if (x_142 == 0)
{
return x_123;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_123, 0);
x_144 = lean_ctor_get(x_123, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_123);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint64_t x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_18, 0);
x_147 = lean_ctor_get(x_18, 1);
x_148 = lean_ctor_get(x_18, 2);
x_149 = lean_ctor_get(x_18, 3);
x_150 = lean_ctor_get_uint64(x_18, sizeof(void*)*4);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_147);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_151 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_147, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_148);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_154 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_148, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_149);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_157 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_149, x_6, x_7, x_8, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_160, 0, x_146);
lean_ctor_set(x_160, 1, x_147);
lean_ctor_set(x_160, 2, x_148);
lean_ctor_set(x_160, 3, x_149);
lean_ctor_set_uint64(x_160, sizeof(void*)*4, x_150);
x_161 = lean_expr_update_let(x_160, x_152, x_155, x_158);
x_162 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_161, x_6, x_7, x_8, x_159);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_165 = x_157;
} else {
 lean_dec_ref(x_157);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_ctor_get(x_154, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_169 = x_154;
} else {
 lean_dec_ref(x_154);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_151, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_151, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_173 = x_151;
} else {
 lean_dec_ref(x_151);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
case 10:
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_10, 1);
lean_inc(x_175);
lean_dec(x_10);
x_176 = !lean_is_exclusive(x_18);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_18, 0);
x_178 = lean_ctor_get(x_18, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_178);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_179 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_178, x_6, x_7, x_8, x_175);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_expr_update_mdata(x_18, x_180);
x_183 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_182, x_6, x_7, x_8, x_181);
return x_183;
}
else
{
uint8_t x_184; 
lean_free_object(x_18);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_179);
if (x_184 == 0)
{
return x_179;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_179, 0);
x_186 = lean_ctor_get(x_179, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_179);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; uint64_t x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_18, 0);
x_189 = lean_ctor_get(x_18, 1);
x_190 = lean_ctor_get_uint64(x_18, sizeof(void*)*2);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_189);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_191 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_189, x_6, x_7, x_8, x_175);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_194, 0, x_188);
lean_ctor_set(x_194, 1, x_189);
lean_ctor_set_uint64(x_194, sizeof(void*)*2, x_190);
x_195 = lean_expr_update_mdata(x_194, x_192);
x_196 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_195, x_6, x_7, x_8, x_193);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_191, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_191, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_199 = x_191;
} else {
 lean_dec_ref(x_191);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
case 11:
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_10, 1);
lean_inc(x_201);
lean_dec(x_10);
x_202 = !lean_is_exclusive(x_18);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_18, 0);
x_204 = lean_ctor_get(x_18, 1);
x_205 = lean_ctor_get(x_18, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_205);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_206 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_205, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_expr_update_proj(x_18, x_207);
x_210 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_209, x_6, x_7, x_8, x_208);
return x_210;
}
else
{
uint8_t x_211; 
lean_free_object(x_18);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_206);
if (x_211 == 0)
{
return x_206;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_206, 0);
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_206);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint64_t x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_18, 0);
x_216 = lean_ctor_get(x_18, 1);
x_217 = lean_ctor_get(x_18, 2);
x_218 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_217);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_219 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_1, x_2, x_3, x_4, x_217, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_222, 0, x_215);
lean_ctor_set(x_222, 1, x_216);
lean_ctor_set(x_222, 2, x_217);
lean_ctor_set_uint64(x_222, sizeof(void*)*3, x_218);
x_223 = lean_expr_update_proj(x_222, x_220);
x_224 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_223, x_6, x_7, x_8, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
default: 
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_10, 1);
lean_inc(x_229);
lean_dec(x_10);
x_230 = l_Lean_Core_transform_visit_visitPost___at_Lean_Core_betaReduce___spec__3(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_229);
return x_230;
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_10);
if (x_231 == 0)
{
return x_10;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_10, 0);
x_233 = lean_ctor_get(x_10, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_10);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
lean_ctor_set(x_5, 1, x_9);
x_12 = lean_apply_4(x_2, x_3, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_17);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_19);
x_21 = lean_apply_4(x_2, x_3, x_20, x_6, x_7);
return x_21;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg___lambda__1(x_6, x_1, x_2, x_9, x_3, x_4, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_20 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_19, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 1, x_13);
x_16 = l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___at_Lean_Core_betaReduce___spec__7(x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = l_ReaderT_bind___at_Lean_Core_betaReduce___spec__6___at_Lean_Core_betaReduce___spec__7(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_10, x_11);
return x_25;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___lambda__1(x_11, x_1, x_2, x_3, x_4, x_5, x_7, x_14, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_25 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_24, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_6);
lean_inc(x_4);
lean_inc(x_8);
lean_inc(x_7);
x_11 = lean_apply_5(x_4, lean_box(0), x_10, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_13, x_5);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_free_object(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(x_1, x_2, x_3, x_4, x_5, x_3, x_6, x_7, x_8, x_14);
lean_dec(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2), 3, 2);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_17);
x_20 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_apply_5(x_4, lean_box(0), x_20, x_7, x_8, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_35, x_5);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(x_1, x_2, x_3, x_4, x_5, x_3, x_6, x_7, x_8, x_36);
lean_dec(x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2), 3, 2);
lean_closure_set(x_41, 0, x_5);
lean_closure_set(x_41, 1, x_39);
x_42 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_42, 0, x_6);
lean_closure_set(x_42, 1, x_41);
x_43 = lean_apply_5(x_4, lean_box(0), x_42, x_7, x_8, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_36);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_11, 0);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_11);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_box(0);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1;
lean_inc(x_5);
lean_inc(x_12);
x_15 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2(x_2, x_3, x_7, x_14, x_1, x_12, x_4, x_5, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_5, x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_12, x_19);
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_headBeta(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__2___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_4);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_5);
x_9 = lean_apply_5(x_2, lean_box(0), x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_11, x_3);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_14 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1;
x_15 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(x_14, x_15, x_1, x_2, x_3, x_1, x_4, x_5, x_6, x_12);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2), 3, 2);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_17);
x_20 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_apply_5(x_2, lean_box(0), x_20, x_5, x_6, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_35, x_3);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1;
x_39 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(x_38, x_39, x_1, x_2, x_3, x_1, x_4, x_5, x_6, x_36);
lean_dec(x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2), 3, 2);
lean_closure_set(x_43, 0, x_3);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_44, 0, x_4);
lean_closure_set(x_44, 1, x_43);
x_45 = lean_apply_5(x_2, lean_box(0), x_44, x_5, x_6, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
lean_dec(x_37);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_36);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_9);
if (x_59 == 0)
{
return x_9;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___at_Lean_Core_betaReduce___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_box(0);
x_6 = lean_st_ref_get(x_3, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1;
lean_inc(x_3);
lean_inc(x_10);
x_13 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11(x_5, x_12, x_1, x_10, x_2, x_3, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_15);
lean_dec(x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_10, x_17);
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Core_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___at_Lean_Core_betaReduce___spec__10(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_betaReduce___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Core_betaReduce___spec__4(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Core_withIncRecDepth___at_Lean_Core_betaReduce___spec__8___at_Lean_Core_betaReduce___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = 1;
x_14 = x_1 + x_13;
x_15 = x_12;
x_16 = lean_array_uset(x_2, x_1, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14, x_16, x_11);
return x_17;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_9 < x_8;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = x_10;
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_array_uget(x_10, x_9);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_10, x_9, x_18);
x_20 = x_17;
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_11);
x_23 = lean_box_usize(x_9);
x_24 = lean_box_usize(x_8);
x_25 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1___boxed), 12, 11);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_19);
lean_closure_set(x_25, 2, x_1);
lean_closure_set(x_25, 3, x_2);
lean_closure_set(x_25, 4, x_3);
lean_closure_set(x_25, 5, x_4);
lean_closure_set(x_25, 6, x_5);
lean_closure_set(x_25, 7, x_6);
lean_closure_set(x_25, 8, x_7);
lean_closure_set(x_25, 9, x_24);
lean_closure_set(x_25, 10, x_11);
x_26 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_22, x_25);
return x_26;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkAppN(x_1, x_10);
x_12 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = x_1;
x_15 = lean_box_usize(x_13);
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___boxed), 11, 10);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
lean_closure_set(x_17, 6, x_8);
lean_closure_set(x_17, 7, x_15);
lean_closure_set(x_17, 8, x_16);
lean_closure_set(x_17, 9, x_14);
x_18 = x_17;
lean_inc(x_9);
x_19 = lean_apply_1(x_18, x_9);
x_20 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_closure_set(x_20, 7, x_8);
lean_closure_set(x_20, 8, x_9);
x_21 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_array_set(x_10, x_11, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_11, x_16);
lean_dec(x_11);
x_9 = x_13;
x_10 = x_15;
x_11 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_12);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2), 11, 10);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_12);
lean_closure_set(x_20, 9, x_8);
x_21 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg), 12, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOfReaderT___rarg___lambda__2), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___rarg), 6, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_update_mdata(x_1, x_10);
x_13 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint64(x_17, sizeof(void*)*2, x_16);
x_18 = lean_expr_update_mdata(x_17, x_10);
x_19 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_9);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_1);
x_20 = l_Lean_instInhabitedExpr;
x_21 = l_Lean_Expr_updateMData_x21___closed__3;
x_22 = lean_panic_fn(x_20, x_21);
x_23 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22, x_9);
return x_23;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_update_proj(x_1, x_10);
x_13 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_18 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint64(x_18, sizeof(void*)*3, x_17);
x_19 = lean_expr_update_proj(x_18, x_10);
x_20 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_9);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_1);
x_21 = l_Lean_instInhabitedExpr;
x_22 = l_Lean_Expr_updateProj_x21___closed__3;
x_23 = lean_panic_fn(x_21, x_22);
x_24 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_9);
return x_24;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
switch (lean_obj_tag(x_15)) {
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux(x_15, x_16);
x_18 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_15, x_19, x_21, x_8);
return x_22;
}
case 6:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_23 = l_Array_empty___closed__1;
x_24 = l_Lean_Meta_transform_visit_visitLambda___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_15, x_8);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_25 = l_Array_empty___closed__1;
x_26 = l_Lean_Meta_transform_visit_visitForall___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_25, x_15, x_8);
return x_26;
}
case 8:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
x_27 = l_Array_empty___closed__1;
x_28 = l_Lean_Meta_transform_visit_visitLet___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_15, x_8);
return x_28;
}
case 10:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_29, x_8);
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1), 10, 9);
lean_closure_set(x_31, 0, x_15);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_2);
lean_closure_set(x_31, 3, x_3);
lean_closure_set(x_31, 4, x_4);
lean_closure_set(x_31, 5, x_5);
lean_closure_set(x_31, 6, x_6);
lean_closure_set(x_31, 7, x_7);
lean_closure_set(x_31, 8, x_8);
x_32 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_30, x_31);
return x_32;
}
case 11:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_15, 2);
lean_inc(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_8);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__2), 10, 9);
lean_closure_set(x_35, 0, x_15);
lean_closure_set(x_35, 1, x_1);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_3);
lean_closure_set(x_35, 4, x_4);
lean_closure_set(x_35, 5, x_5);
lean_closure_set(x_35, 6, x_6);
lean_closure_set(x_35, 7, x_7);
lean_closure_set(x_35, 8, x_8);
x_36 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
default: 
{
lean_object* x_37; 
lean_dec(x_9);
x_37 = l_Lean_Meta_transform_visit_visitPost___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_8);
return x_37;
}
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_4);
x_12 = lean_apply_1(x_4, x_8);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__3), 10, 9);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_11);
lean_closure_set(x_14, 8, x_9);
x_15 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_12, x_14);
return x_15;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
lean_ctor_set(x_8, 1, x_12);
x_15 = lean_apply_1(x_2, x_3);
x_16 = lean_apply_7(x_4, lean_box(0), x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_8, 3);
x_20 = lean_ctor_get(x_8, 4);
x_21 = lean_ctor_get(x_8, 5);
x_22 = lean_ctor_get(x_8, 6);
x_23 = lean_ctor_get(x_8, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = lean_apply_1(x_2, x_3);
x_26 = lean_apply_7(x_4, lean_box(0), x_25, x_6, x_7, x_24, x_9, x_10);
return x_26;
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__1(x_9, x_1, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_15 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_14, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__2), 8, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_20);
lean_inc(x_2);
x_23 = l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_11);
x_24 = lean_apply_7(x_12, lean_box(0), x_23, x_14, x_15, x_16, x_17, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 2);
x_27 = lean_ctor_get(x_16, 3);
x_28 = lean_ctor_get(x_16, 4);
x_29 = lean_ctor_get(x_16, 5);
x_30 = lean_ctor_get(x_16, 6);
x_31 = lean_ctor_get(x_16, 7);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_30);
lean_ctor_set(x_32, 7, x_31);
lean_inc(x_2);
x_33 = l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___at_Lean_Meta_transform_visit___spec__4___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_11);
x_34 = lean_apply_7(x_12, lean_box(0), x_33, x_14, x_15, x_32, x_17, x_18);
return x_34;
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__1(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_17);
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
lean_dec(x_1);
x_22 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_23 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_22, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__2), 16, 10);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
lean_closure_set(x_16, 7, x_8);
lean_closure_set(x_16, 8, x_13);
lean_closure_set(x_16, 9, x_12);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_18, 0, x_10);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc_n(x_1, 2);
x_12 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1, x_3, x_6, x_9);
lean_dec(x_6);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__8), 6, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_7);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_10);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_15);
return x_18;
}
}
}
lean_object* l_Lean_Meta_transform_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, x_9);
lean_inc(x_7);
x_12 = lean_apply_2(x_7, lean_box(0), x_11);
lean_inc(x_1);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_1);
lean_inc(x_10);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___rarg___lambda__1), 11, 10);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
lean_closure_set(x_15, 7, x_8);
lean_closure_set(x_15, 8, x_9);
lean_closure_set(x_15, 9, x_10);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Meta_transform_visit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitPost___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_8);
return x_15;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitPost___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_10 = lean_apply_1(x_5, x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitPost___rarg___lambda__1), 9, 8);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
lean_closure_set(x_12, 7, x_9);
x_13 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_transform_visit_visitPost(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitPost___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_4, x_2);
x_11 = lean_apply_7(x_3, lean_box(0), x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_box(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2___boxed), 11, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_7);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_push(x_1, x_12);
x_19 = l_Lean_Meta_transform_visit_visitLambda___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_9, x_10);
x_20 = lean_apply_7(x_11, lean_box(0), x_19, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__1___boxed), 17, 11);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_closure_set(x_20, 7, x_8);
lean_closure_set(x_20, 8, x_9);
lean_closure_set(x_20, 9, x_10);
lean_closure_set(x_20, 10, x_14);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_11, x_12, x_13, x_20, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_box(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__2___boxed), 19, 13);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_9);
lean_closure_set(x_20, 9, x_16);
lean_closure_set(x_20, 10, x_13);
lean_closure_set(x_20, 11, x_19);
lean_closure_set(x_20, 12, x_15);
x_21 = lean_apply_2(x_18, lean_box(0), x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_22, 0, x_11);
x_23 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___boxed), 16, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_transform_visit_visitPost___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = 0;
x_13 = 1;
x_14 = lean_box(x_12);
x_15 = lean_box(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 9, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = lean_apply_2(x_2, lean_box(0), x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_6);
lean_closure_set(x_18, 5, x_7);
lean_closure_set(x_18, 6, x_8);
lean_closure_set(x_18, 7, x_9);
x_19 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = (uint8_t)((x_1 << 24) >> 61);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_4, x_7, x_11, x_14, x_13, x_12);
lean_dec(x_7);
return x_15;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_9) == 6)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_15 = lean_expr_instantiate_rev(x_12, x_8);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_10);
x_18 = lean_box_uint64(x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3___boxed), 13, 12);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
lean_closure_set(x_19, 7, x_7);
lean_closure_set(x_19, 8, x_8);
lean_closure_set(x_19, 9, x_13);
lean_closure_set(x_19, 10, x_11);
lean_closure_set(x_19, 11, x_10);
x_20 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_10);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__2), 11, 10);
lean_closure_set(x_24, 0, x_8);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_6);
lean_closure_set(x_24, 7, x_7);
lean_closure_set(x_24, 8, x_10);
lean_closure_set(x_24, 9, x_22);
x_25 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_box(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2___boxed), 11, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_7);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_push(x_1, x_12);
x_19 = l_Lean_Meta_transform_visit_visitForall___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_9, x_10);
x_20 = lean_apply_7(x_11, lean_box(0), x_19, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__1___boxed), 17, 11);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_closure_set(x_20, 7, x_8);
lean_closure_set(x_20, 8, x_9);
lean_closure_set(x_20, 9, x_10);
lean_closure_set(x_20, 10, x_14);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_11, x_12, x_13, x_20, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_box(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__2___boxed), 19, 13);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_9);
lean_closure_set(x_20, 9, x_16);
lean_closure_set(x_20, 10, x_13);
lean_closure_set(x_20, 11, x_19);
lean_closure_set(x_20, 12, x_15);
x_21 = lean_apply_2(x_18, lean_box(0), x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_22, 0, x_11);
x_23 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___boxed), 16, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = 0;
x_13 = 1;
x_14 = lean_box(x_12);
x_15 = lean_box(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 9, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = lean_apply_2(x_2, lean_box(0), x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_6);
lean_closure_set(x_18, 5, x_7);
lean_closure_set(x_18, 6, x_8);
lean_closure_set(x_18, 7, x_9);
x_19 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = (uint8_t)((x_1 << 24) >> 61);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2, x_4, x_7, x_11, x_14, x_13, x_12);
lean_dec(x_7);
return x_15;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_15 = lean_expr_instantiate_rev(x_12, x_8);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_10);
x_18 = lean_box_uint64(x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2___boxed), 13, 12);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
lean_closure_set(x_19, 7, x_7);
lean_closure_set(x_19, 8, x_8);
lean_closure_set(x_19, 9, x_13);
lean_closure_set(x_19, 10, x_11);
lean_closure_set(x_19, 11, x_10);
x_20 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_10);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__1), 11, 10);
lean_closure_set(x_24, 0, x_8);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_6);
lean_closure_set(x_24, 7, x_7);
lean_closure_set(x_24, 8, x_10);
lean_closure_set(x_24, 9, x_22);
x_25 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___lambda__1), 11, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_7);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_push(x_1, x_12);
x_19 = l_Lean_Meta_transform_visit_visitLet___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_9, x_10);
x_20 = lean_apply_7(x_11, lean_box(0), x_19, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__1___boxed), 17, 11);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_closure_set(x_20, 7, x_8);
lean_closure_set(x_20, 8, x_9);
lean_closure_set(x_20, 9, x_10);
lean_closure_set(x_20, 10, x_14);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_11, x_12, x_13, x_20, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__2___boxed), 19, 13);
lean_closure_set(x_19, 0, x_8);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
lean_closure_set(x_19, 7, x_7);
lean_closure_set(x_19, 8, x_9);
lean_closure_set(x_19, 9, x_16);
lean_closure_set(x_19, 10, x_13);
lean_closure_set(x_19, 11, x_14);
lean_closure_set(x_19, 12, x_15);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__5___rarg___lambda__3), 2, 1);
lean_closure_set(x_21, 0, x_11);
x_22 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___boxed), 16, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
lean_closure_set(x_14, 7, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_14 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1, x_3, x_6, x_10, x_11, x_13, x_12);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_expr_instantiate_rev(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Meta_transform_visit___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__2), 13, 12);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_6);
lean_closure_set(x_17, 4, x_7);
lean_closure_set(x_17, 5, x_8);
lean_closure_set(x_17, 6, x_9);
lean_closure_set(x_17, 7, x_2);
lean_closure_set(x_17, 8, x_11);
lean_closure_set(x_17, 9, x_12);
lean_closure_set(x_17, 10, x_14);
lean_closure_set(x_17, 11, x_10);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_9) == 8)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_expr_instantiate_rev(x_12, x_8);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_10);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3___boxed), 14, 13);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_4);
lean_closure_set(x_18, 6, x_5);
lean_closure_set(x_18, 7, x_6);
lean_closure_set(x_18, 8, x_7);
lean_closure_set(x_18, 9, x_10);
lean_closure_set(x_18, 10, x_14);
lean_closure_set(x_18, 11, x_11);
lean_closure_set(x_18, 12, x_16);
x_19 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_10);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__1), 11, 10);
lean_closure_set(x_23, 0, x_8);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_closure_set(x_23, 6, x_6);
lean_closure_set(x_23, 7, x_7);
lean_closure_set(x_23, 8, x_10);
lean_closure_set(x_23, 9, x_21);
x_24 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14, x_11, x_12);
return x_15;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_1);
return x_19;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__5___at_Lean_Meta_transform_visit___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_14);
lean_dec(x_14);
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__1___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17, x_15, x_16);
lean_dec(x_12);
return x_18;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_12);
lean_dec(x_12);
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_14);
lean_dec(x_14);
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__1___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17, x_15, x_16);
lean_dec(x_12);
return x_18;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__1___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
return x_17;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_1(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg___lambda__1___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_mk_ref(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg___lambda__4___boxed), 6, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_StateRefT_x27_run___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg___lambda__5), 5, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_transform___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg___lambda__3___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_transform___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg___lambda__2), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Meta_transform___rarg___closed__1;
lean_inc(x_2);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
lean_inc(x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg___lambda__6), 10, 9);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_8);
lean_closure_set(x_12, 7, x_4);
lean_closure_set(x_12, 8, x_9);
lean_inc(x_9);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_StateRefT_x27_run_x27___rarg___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_transform(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_transform___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_transform___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_transform___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_transform___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_zetaReduce_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_zetaReduce_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_zetaReduce_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_zetaReduce_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_zetaReduce_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Meta_zetaReduce_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_zetaReduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_local_ctx_find(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_LocalDecl_value_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = l_Lean_Expr_hasFVar(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_zetaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lambda__1___boxed), 5, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2;
x_10 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_zetaReduce___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_zetaReduce___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_zetaReduce(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Transform(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1);
l_Lean_Core_transform___rarg___closed__1 = _init_l_Lean_Core_transform___rarg___closed__1();
lean_mark_persistent(l_Lean_Core_transform___rarg___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Core_betaReduce___spec__5___boxed__const__1);
l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1 = _init_l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1();
lean_mark_persistent(l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1___closed__1);
l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1 = _init_l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1();
lean_mark_persistent(l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__1);
l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2 = _init_l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2();
lean_mark_persistent(l_Lean_Core_transform_visit___at_Lean_Core_betaReduce___spec__2___at_Lean_Core_betaReduce___spec__11___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1);
l_Lean_Meta_transform___rarg___closed__1 = _init_l_Lean_Meta_transform___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_transform___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
