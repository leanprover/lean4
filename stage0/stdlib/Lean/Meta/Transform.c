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
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda_match__1(lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12(lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Meta_transform_visit_visitLambda(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1;
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1018____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7(lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Core_transform_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2(lean_object*);
lean_object* l_StateRefT_x27_run___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall_match__1(lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__9(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_transform_visit_visitLet_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_match__2(lean_object*);
lean_object* l_Lean_Meta_transform___rarg___closed__1;
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11(lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2(lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost_match__1(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__9(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__2;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_match__1(lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10(lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4(lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8(lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_visitPost___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost_match__1(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_match__2(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost(lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_run_x27___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instInhabitedExpr;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__2___boxed__const__1;
lean_object* l_Lean_Meta_transform_visit_visitLet_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8(lean_object*);
lean_object* l_Lean_Meta_mkForallFVarsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVarsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4(lean_object*);
lean_object* l_Lean_Meta_transform___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_transform_visit___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOfReaderT___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7(lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4(lean_object*);
lean_object* l_Lean_Meta_transform_visit_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Core_transform_visit___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform_visit___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_transform_visit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Core_transform_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit_match__2___rarg), 3, 0);
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
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 4);
x_19 = lean_ctor_get(x_6, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
x_21 = lean_apply_1(x_2, x_3);
x_22 = lean_apply_5(x_4, lean_box(0), x_21, x_20, x_7, x_8);
return x_22;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1(x_7, x_1, x_2, x_3, x_10, x_4, x_5, x_6);
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
x_13 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1___rarg(x_12, x_4, x_5, x_6);
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
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__2), 6, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_24 = l_Lean_Expr_instInhabitedExpr;
x_25 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_26 = lean_panic_fn(x_24, x_25);
x_27 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_8);
return x_27;
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_13 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__1), 10, 9);
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
lean_object* l_Lean_Core_transform_visit___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_24 = l_Lean_Expr_instInhabitedExpr;
x_25 = l_Lean_Expr_updateForallE_x21___closed__2;
x_26 = lean_panic_fn(x_24, x_25);
x_27 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_8);
return x_27;
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_13 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__3), 10, 9);
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
lean_object* l_Lean_Core_transform_visit___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_23 = l_Lean_Expr_instInhabitedExpr;
x_24 = l_Lean_Expr_updateLet_x21___closed__2;
x_25 = lean_panic_fn(x_23, x_24);
x_26 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_25, x_8);
return x_26;
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_14 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__5), 11, 10);
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
lean_object* l_Lean_Core_transform_visit___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_14 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__6), 12, 11);
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
lean_object* l_Lean_Core_transform_visit___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_Expr_instInhabitedExpr;
x_20 = l_Lean_Expr_updateMData_x21___closed__3;
x_21 = lean_panic_fn(x_19, x_20);
x_22 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_8);
return x_22;
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_20 = l_Lean_Expr_instInhabitedExpr;
x_21 = l_Lean_Expr_updateProj_x21___closed__3;
x_22 = lean_panic_fn(x_20, x_21);
x_23 = l_Lean_Core_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_8);
return x_23;
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
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
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
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
x_21 = l_Lean_Expr_withAppAux___at_Lean_Core_transform_visit___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_18, x_20, x_9);
return x_21;
}
case 6:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_9);
lean_inc(x_7);
x_25 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__2), 11, 10);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_23);
lean_closure_set(x_25, 7, x_9);
lean_closure_set(x_25, 8, x_14);
lean_closure_set(x_25, 9, x_7);
x_26 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 2);
lean_inc(x_28);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_27, x_9);
lean_inc(x_7);
x_30 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__4), 11, 10);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_5);
lean_closure_set(x_30, 5, x_6);
lean_closure_set(x_30, 6, x_28);
lean_closure_set(x_30, 7, x_9);
lean_closure_set(x_30, 8, x_14);
lean_closure_set(x_30, 9, x_7);
x_31 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_29, x_30);
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
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_32, x_9);
lean_inc(x_7);
x_36 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__7), 12, 11);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_4);
lean_closure_set(x_36, 4, x_5);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_33);
lean_closure_set(x_36, 7, x_9);
lean_closure_set(x_36, 8, x_34);
lean_closure_set(x_36, 9, x_14);
lean_closure_set(x_36, 10, x_7);
x_37 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_35, x_36);
return x_37;
}
case 10:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_38, x_9);
x_40 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__8), 9, 8);
lean_closure_set(x_40, 0, x_14);
lean_closure_set(x_40, 1, x_1);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_3);
lean_closure_set(x_40, 4, x_4);
lean_closure_set(x_40, 5, x_5);
lean_closure_set(x_40, 6, x_6);
lean_closure_set(x_40, 7, x_9);
x_41 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_39, x_40);
return x_41;
}
case 11:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_14, 2);
lean_inc(x_42);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_Core_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_42, x_9);
x_44 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__9), 9, 8);
lean_closure_set(x_44, 0, x_14);
lean_closure_set(x_44, 1, x_1);
lean_closure_set(x_44, 2, x_2);
lean_closure_set(x_44, 3, x_3);
lean_closure_set(x_44, 4, x_4);
lean_closure_set(x_44, 5, x_5);
lean_closure_set(x_44, 6, x_6);
lean_closure_set(x_44, 7, x_9);
x_45 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_43, x_44);
return x_45;
}
default: 
{
lean_object* x_46; 
lean_dec(x_7);
x_46 = l_Lean_Core_transform_visit_visitPost___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_9);
return x_46;
}
}
}
}
}
lean_object* l_Lean_Core_transform_visit___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_apply_1(x_1, x_2);
x_12 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__10), 9, 7);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_7);
lean_closure_set(x_13, 6, x_8);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_transform_visit___spec__3___rarg), 6, 5);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, lean_box(0));
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
lean_inc(x_9);
lean_inc(x_3);
x_15 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg(x_3, x_4, x_6, x_14, x_9);
lean_dec(x_6);
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__8), 6, 5);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_9);
lean_closure_set(x_16, 2, x_7);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_8);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_2(x_20, lean_box(0), x_18);
return x_21;
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
x_14 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___rarg___lambda__11), 10, 9);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_2);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_9);
lean_closure_set(x_14, 8, x_8);
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
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
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
lean_object* l_Lean_Meta_transform_visit_visitPost_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_transform_visit_visitPost_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitPost_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Meta_transform_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_transform_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_transform_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_match__2___rarg), 3, 0);
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
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_8, 3);
x_20 = lean_ctor_get(x_8, 4);
x_21 = lean_ctor_get(x_8, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_apply_1(x_2, x_3);
x_24 = lean_apply_7(x_4, lean_box(0), x_23, x_6, x_7, x_22, x_9, x_10);
return x_24;
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1(x_9, x_1, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8);
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
x_15 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1018____spec__1___rarg(x_14, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__2), 8, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3), 2, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_20 = l_Lean_Expr_instInhabitedExpr;
x_21 = l_Lean_Expr_updateMData_x21___closed__3;
x_22 = lean_panic_fn(x_20, x_21);
x_23 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22, x_9);
return x_23;
}
}
}
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_21 = l_Lean_Expr_instInhabitedExpr;
x_22 = l_Lean_Expr_updateProj_x21___closed__3;
x_23 = lean_panic_fn(x_21, x_22);
x_24 = l_Lean_Meta_transform_visit_visitPost___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_9);
return x_24;
}
}
}
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
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
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
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
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_19, x_21, x_10);
return x_22;
}
case 6:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_23 = l_Array_empty___closed__1;
x_24 = l_Lean_Meta_transform_visit_visitForall___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_15, x_10);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_25 = l_Array_empty___closed__1;
x_26 = l_Lean_Meta_transform_visit_visitLambda___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_25, x_15, x_10);
return x_26;
}
case 8:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_27 = l_Array_empty___closed__1;
x_28 = l_Lean_Meta_transform_visit_visitLet___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_15, x_10);
return x_28;
}
case 10:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_29, x_10);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___rarg___lambda__1), 10, 9);
lean_closure_set(x_31, 0, x_15);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_2);
lean_closure_set(x_31, 3, x_3);
lean_closure_set(x_31, 4, x_4);
lean_closure_set(x_31, 5, x_5);
lean_closure_set(x_31, 6, x_6);
lean_closure_set(x_31, 7, x_7);
lean_closure_set(x_31, 8, x_10);
x_32 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_30, x_31);
return x_32;
}
case 11:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_15, 2);
lean_inc(x_33);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_10);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___rarg___lambda__2), 10, 9);
lean_closure_set(x_35, 0, x_15);
lean_closure_set(x_35, 1, x_1);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_3);
lean_closure_set(x_35, 4, x_4);
lean_closure_set(x_35, 5, x_5);
lean_closure_set(x_35, 6, x_6);
lean_closure_set(x_35, 7, x_7);
lean_closure_set(x_35, 8, x_10);
x_36 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
default: 
{
lean_object* x_37; 
lean_dec(x_8);
x_37 = l_Lean_Meta_transform_visit_visitPost___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_10);
return x_37;
}
}
}
}
}
lean_object* l_Lean_Meta_transform_visit___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
lean_inc(x_2);
x_12 = lean_apply_1(x_1, x_2);
x_13 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___rarg___lambda__3), 10, 8);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_5);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
lean_closure_set(x_14, 7, x_9);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_transform_visit___spec__3___rarg), 6, 5);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, lean_box(0));
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
lean_inc(x_10);
lean_inc(x_3);
x_16 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg(x_3, x_5, x_7, lean_box(0), x_15, x_10);
lean_dec(x_7);
lean_inc(x_9);
x_17 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__8), 6, 5);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_8);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_9);
x_18 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_19);
return x_22;
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
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___rarg___lambda__4), 11, 10);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_5);
lean_closure_set(x_15, 6, x_6);
lean_closure_set(x_15, 7, x_7);
lean_closure_set(x_15, 8, x_10);
lean_closure_set(x_15, 9, x_9);
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
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_4, x_2);
x_11 = lean_apply_7(x_3, lean_box(0), x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_box(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2___boxed), 11, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_7);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3), 2, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg___boxed), 5, 0);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_10);
x_13 = l_Lean_Meta_transform_visit_visitLambda___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_9, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__9(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = (uint8_t)((x_1 << 24) >> 61);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__8), 11, 9);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_7);
lean_closure_set(x_15, 6, x_8);
lean_closure_set(x_15, 7, x_9);
lean_closure_set(x_15, 8, x_10);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg(x_3, x_5, x_8, lean_box(0), x_11, x_14, x_13, x_15, x_12);
lean_dec(x_8);
return x_16;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_10);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__2), 11, 10);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_8);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_1);
lean_closure_set(x_14, 5, x_3);
lean_closure_set(x_14, 6, x_4);
lean_closure_set(x_14, 7, x_5);
lean_closure_set(x_14, 8, x_7);
lean_closure_set(x_14, 9, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_10);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__3), 11, 10);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_8);
lean_closure_set(x_19, 3, x_10);
lean_closure_set(x_19, 4, x_1);
lean_closure_set(x_19, 5, x_3);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_5);
lean_closure_set(x_19, 8, x_7);
lean_closure_set(x_19, 9, x_17);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
case 2:
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
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__4), 11, 10);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_6);
lean_closure_set(x_24, 2, x_8);
lean_closure_set(x_24, 3, x_10);
lean_closure_set(x_24, 4, x_1);
lean_closure_set(x_24, 5, x_3);
lean_closure_set(x_24, 6, x_4);
lean_closure_set(x_24, 7, x_5);
lean_closure_set(x_24, 8, x_7);
lean_closure_set(x_24, 9, x_22);
x_25 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_10);
lean_inc(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__5), 11, 10);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_6);
lean_closure_set(x_29, 2, x_8);
lean_closure_set(x_29, 3, x_10);
lean_closure_set(x_29, 4, x_1);
lean_closure_set(x_29, 5, x_3);
lean_closure_set(x_29, 6, x_4);
lean_closure_set(x_29, 7, x_5);
lean_closure_set(x_29, 8, x_7);
lean_closure_set(x_29, 9, x_27);
x_30 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_28, x_29);
return x_30;
}
case 4:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_10);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__6), 11, 10);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_8);
lean_closure_set(x_34, 3, x_10);
lean_closure_set(x_34, 4, x_1);
lean_closure_set(x_34, 5, x_3);
lean_closure_set(x_34, 6, x_4);
lean_closure_set(x_34, 7, x_5);
lean_closure_set(x_34, 8, x_7);
lean_closure_set(x_34, 9, x_32);
x_35 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_34);
return x_35;
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
lean_inc(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__7), 11, 10);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_6);
lean_closure_set(x_39, 2, x_8);
lean_closure_set(x_39, 3, x_10);
lean_closure_set(x_39, 4, x_1);
lean_closure_set(x_39, 5, x_3);
lean_closure_set(x_39, 6, x_4);
lean_closure_set(x_39, 7, x_5);
lean_closure_set(x_39, 8, x_7);
lean_closure_set(x_39, 9, x_37);
x_40 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_45 = lean_expr_instantiate_rev(x_42, x_8);
lean_dec(x_42);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_45, x_10);
x_48 = lean_box_uint64(x_44);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__9___boxed), 13, 12);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_8);
lean_closure_set(x_49, 2, x_1);
lean_closure_set(x_49, 3, x_2);
lean_closure_set(x_49, 4, x_3);
lean_closure_set(x_49, 5, x_4);
lean_closure_set(x_49, 6, x_5);
lean_closure_set(x_49, 7, x_6);
lean_closure_set(x_49, 8, x_7);
lean_closure_set(x_49, 9, x_43);
lean_closure_set(x_49, 10, x_41);
lean_closure_set(x_49, 11, x_10);
x_50 = lean_apply_4(x_46, lean_box(0), lean_box(0), x_47, x_49);
return x_50;
}
case 7:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_51, x_10);
lean_inc(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__10), 11, 10);
lean_closure_set(x_54, 0, x_2);
lean_closure_set(x_54, 1, x_6);
lean_closure_set(x_54, 2, x_8);
lean_closure_set(x_54, 3, x_10);
lean_closure_set(x_54, 4, x_1);
lean_closure_set(x_54, 5, x_3);
lean_closure_set(x_54, 6, x_4);
lean_closure_set(x_54, 7, x_5);
lean_closure_set(x_54, 8, x_7);
lean_closure_set(x_54, 9, x_52);
x_55 = lean_apply_4(x_52, lean_box(0), lean_box(0), x_53, x_54);
return x_55;
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_56, x_10);
lean_inc(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__11), 11, 10);
lean_closure_set(x_59, 0, x_2);
lean_closure_set(x_59, 1, x_6);
lean_closure_set(x_59, 2, x_8);
lean_closure_set(x_59, 3, x_10);
lean_closure_set(x_59, 4, x_1);
lean_closure_set(x_59, 5, x_3);
lean_closure_set(x_59, 6, x_4);
lean_closure_set(x_59, 7, x_5);
lean_closure_set(x_59, 8, x_7);
lean_closure_set(x_59, 9, x_57);
x_60 = lean_apply_4(x_57, lean_box(0), lean_box(0), x_58, x_59);
return x_60;
}
case 9:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_63 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_61, x_10);
lean_inc(x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__12), 11, 10);
lean_closure_set(x_64, 0, x_2);
lean_closure_set(x_64, 1, x_6);
lean_closure_set(x_64, 2, x_8);
lean_closure_set(x_64, 3, x_10);
lean_closure_set(x_64, 4, x_1);
lean_closure_set(x_64, 5, x_3);
lean_closure_set(x_64, 6, x_4);
lean_closure_set(x_64, 7, x_5);
lean_closure_set(x_64, 8, x_7);
lean_closure_set(x_64, 9, x_62);
x_65 = lean_apply_4(x_62, lean_box(0), lean_box(0), x_63, x_64);
return x_65;
}
case 10:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_66, x_10);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__13), 11, 10);
lean_closure_set(x_69, 0, x_2);
lean_closure_set(x_69, 1, x_6);
lean_closure_set(x_69, 2, x_8);
lean_closure_set(x_69, 3, x_10);
lean_closure_set(x_69, 4, x_1);
lean_closure_set(x_69, 5, x_3);
lean_closure_set(x_69, 6, x_4);
lean_closure_set(x_69, 7, x_5);
lean_closure_set(x_69, 8, x_7);
lean_closure_set(x_69, 9, x_67);
x_70 = lean_apply_4(x_67, lean_box(0), lean_box(0), x_68, x_69);
return x_70;
}
default: 
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_73 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_71, x_10);
lean_inc(x_72);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__14), 11, 10);
lean_closure_set(x_74, 0, x_2);
lean_closure_set(x_74, 1, x_6);
lean_closure_set(x_74, 2, x_8);
lean_closure_set(x_74, 3, x_10);
lean_closure_set(x_74, 4, x_1);
lean_closure_set(x_74, 5, x_3);
lean_closure_set(x_74, 6, x_4);
lean_closure_set(x_74, 7, x_5);
lean_closure_set(x_74, 8, x_7);
lean_closure_set(x_74, 9, x_72);
x_75 = lean_apply_4(x_72, lean_box(0), lean_box(0), x_73, x_74);
return x_75;
}
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
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_box(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2___boxed), 11, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_7);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3), 2, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_10);
x_13 = l_Lean_Meta_transform_visit_visitForall___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_9, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__9(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = (uint8_t)((x_1 << 24) >> 61);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__8), 11, 9);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_7);
lean_closure_set(x_15, 6, x_8);
lean_closure_set(x_15, 7, x_9);
lean_closure_set(x_15, 8, x_10);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg(x_3, x_5, x_8, lean_box(0), x_11, x_14, x_13, x_15, x_12);
lean_dec(x_8);
return x_16;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_10);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__1), 11, 10);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_8);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_1);
lean_closure_set(x_14, 5, x_3);
lean_closure_set(x_14, 6, x_4);
lean_closure_set(x_14, 7, x_5);
lean_closure_set(x_14, 8, x_7);
lean_closure_set(x_14, 9, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_10);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__2), 11, 10);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_8);
lean_closure_set(x_19, 3, x_10);
lean_closure_set(x_19, 4, x_1);
lean_closure_set(x_19, 5, x_3);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_5);
lean_closure_set(x_19, 8, x_7);
lean_closure_set(x_19, 9, x_17);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
case 2:
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
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__3), 11, 10);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_6);
lean_closure_set(x_24, 2, x_8);
lean_closure_set(x_24, 3, x_10);
lean_closure_set(x_24, 4, x_1);
lean_closure_set(x_24, 5, x_3);
lean_closure_set(x_24, 6, x_4);
lean_closure_set(x_24, 7, x_5);
lean_closure_set(x_24, 8, x_7);
lean_closure_set(x_24, 9, x_22);
x_25 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_10);
lean_inc(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__4), 11, 10);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_6);
lean_closure_set(x_29, 2, x_8);
lean_closure_set(x_29, 3, x_10);
lean_closure_set(x_29, 4, x_1);
lean_closure_set(x_29, 5, x_3);
lean_closure_set(x_29, 6, x_4);
lean_closure_set(x_29, 7, x_5);
lean_closure_set(x_29, 8, x_7);
lean_closure_set(x_29, 9, x_27);
x_30 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_28, x_29);
return x_30;
}
case 4:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_10);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__5), 11, 10);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_8);
lean_closure_set(x_34, 3, x_10);
lean_closure_set(x_34, 4, x_1);
lean_closure_set(x_34, 5, x_3);
lean_closure_set(x_34, 6, x_4);
lean_closure_set(x_34, 7, x_5);
lean_closure_set(x_34, 8, x_7);
lean_closure_set(x_34, 9, x_32);
x_35 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_34);
return x_35;
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
lean_inc(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__6), 11, 10);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_6);
lean_closure_set(x_39, 2, x_8);
lean_closure_set(x_39, 3, x_10);
lean_closure_set(x_39, 4, x_1);
lean_closure_set(x_39, 5, x_3);
lean_closure_set(x_39, 6, x_4);
lean_closure_set(x_39, 7, x_5);
lean_closure_set(x_39, 8, x_7);
lean_closure_set(x_39, 9, x_37);
x_40 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_41, x_10);
lean_inc(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__7), 11, 10);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_6);
lean_closure_set(x_44, 2, x_8);
lean_closure_set(x_44, 3, x_10);
lean_closure_set(x_44, 4, x_1);
lean_closure_set(x_44, 5, x_3);
lean_closure_set(x_44, 6, x_4);
lean_closure_set(x_44, 7, x_5);
lean_closure_set(x_44, 8, x_7);
lean_closure_set(x_44, 9, x_42);
x_45 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_43, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_9, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_9, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_50 = lean_expr_instantiate_rev(x_47, x_8);
lean_dec(x_47);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_52 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_50, x_10);
x_53 = lean_box_uint64(x_49);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__9___boxed), 13, 12);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_8);
lean_closure_set(x_54, 2, x_1);
lean_closure_set(x_54, 3, x_2);
lean_closure_set(x_54, 4, x_3);
lean_closure_set(x_54, 5, x_4);
lean_closure_set(x_54, 6, x_5);
lean_closure_set(x_54, 7, x_6);
lean_closure_set(x_54, 8, x_7);
lean_closure_set(x_54, 9, x_48);
lean_closure_set(x_54, 10, x_46);
lean_closure_set(x_54, 11, x_10);
x_55 = lean_apply_4(x_51, lean_box(0), lean_box(0), x_52, x_54);
return x_55;
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_56, x_10);
lean_inc(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__10), 11, 10);
lean_closure_set(x_59, 0, x_2);
lean_closure_set(x_59, 1, x_6);
lean_closure_set(x_59, 2, x_8);
lean_closure_set(x_59, 3, x_10);
lean_closure_set(x_59, 4, x_1);
lean_closure_set(x_59, 5, x_3);
lean_closure_set(x_59, 6, x_4);
lean_closure_set(x_59, 7, x_5);
lean_closure_set(x_59, 8, x_7);
lean_closure_set(x_59, 9, x_57);
x_60 = lean_apply_4(x_57, lean_box(0), lean_box(0), x_58, x_59);
return x_60;
}
case 9:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_63 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_61, x_10);
lean_inc(x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__11), 11, 10);
lean_closure_set(x_64, 0, x_2);
lean_closure_set(x_64, 1, x_6);
lean_closure_set(x_64, 2, x_8);
lean_closure_set(x_64, 3, x_10);
lean_closure_set(x_64, 4, x_1);
lean_closure_set(x_64, 5, x_3);
lean_closure_set(x_64, 6, x_4);
lean_closure_set(x_64, 7, x_5);
lean_closure_set(x_64, 8, x_7);
lean_closure_set(x_64, 9, x_62);
x_65 = lean_apply_4(x_62, lean_box(0), lean_box(0), x_63, x_64);
return x_65;
}
case 10:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_66, x_10);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__12), 11, 10);
lean_closure_set(x_69, 0, x_2);
lean_closure_set(x_69, 1, x_6);
lean_closure_set(x_69, 2, x_8);
lean_closure_set(x_69, 3, x_10);
lean_closure_set(x_69, 4, x_1);
lean_closure_set(x_69, 5, x_3);
lean_closure_set(x_69, 6, x_4);
lean_closure_set(x_69, 7, x_5);
lean_closure_set(x_69, 8, x_7);
lean_closure_set(x_69, 9, x_67);
x_70 = lean_apply_4(x_67, lean_box(0), lean_box(0), x_68, x_69);
return x_70;
}
default: 
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_73 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_71, x_10);
lean_inc(x_72);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___rarg___lambda__13), 11, 10);
lean_closure_set(x_74, 0, x_2);
lean_closure_set(x_74, 1, x_6);
lean_closure_set(x_74, 2, x_8);
lean_closure_set(x_74, 3, x_10);
lean_closure_set(x_74, 4, x_1);
lean_closure_set(x_74, 5, x_3);
lean_closure_set(x_74, 6, x_4);
lean_closure_set(x_74, 7, x_5);
lean_closure_set(x_74, 8, x_7);
lean_closure_set(x_74, 9, x_72);
x_75 = lean_apply_4(x_72, lean_box(0), lean_box(0), x_73, x_74);
return x_75;
}
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
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg___lambda__1), 11, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_7);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___at_Lean_Core_transform_visit___spec__4___rarg___lambda__3), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVarsImp___boxed), 7, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_10);
x_13 = l_Lean_Meta_transform_visit_visitLet___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_9, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__9), 11, 9);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_9);
x_15 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg(x_2, x_4, x_7, lean_box(0), x_10, x_11, x_13, x_14, x_12);
lean_dec(x_7);
return x_15;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__10), 13, 12);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
lean_closure_set(x_17, 6, x_8);
lean_closure_set(x_17, 7, x_9);
lean_closure_set(x_17, 8, x_11);
lean_closure_set(x_17, 9, x_12);
lean_closure_set(x_17, 10, x_14);
lean_closure_set(x_17, 11, x_10);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg(x_1, x_2, x_3, x_11, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__1), 9, 8);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_2);
lean_closure_set(x_13, 6, x_9);
lean_closure_set(x_13, 7, x_4);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_10);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__1), 11, 10);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_8);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_1);
lean_closure_set(x_14, 5, x_3);
lean_closure_set(x_14, 6, x_4);
lean_closure_set(x_14, 7, x_5);
lean_closure_set(x_14, 8, x_7);
lean_closure_set(x_14, 9, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_10);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__2), 11, 10);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_8);
lean_closure_set(x_19, 3, x_10);
lean_closure_set(x_19, 4, x_1);
lean_closure_set(x_19, 5, x_3);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_5);
lean_closure_set(x_19, 8, x_7);
lean_closure_set(x_19, 9, x_17);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
case 2:
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
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__3), 11, 10);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_6);
lean_closure_set(x_24, 2, x_8);
lean_closure_set(x_24, 3, x_10);
lean_closure_set(x_24, 4, x_1);
lean_closure_set(x_24, 5, x_3);
lean_closure_set(x_24, 6, x_4);
lean_closure_set(x_24, 7, x_5);
lean_closure_set(x_24, 8, x_7);
lean_closure_set(x_24, 9, x_22);
x_25 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_10);
lean_inc(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__4), 11, 10);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_6);
lean_closure_set(x_29, 2, x_8);
lean_closure_set(x_29, 3, x_10);
lean_closure_set(x_29, 4, x_1);
lean_closure_set(x_29, 5, x_3);
lean_closure_set(x_29, 6, x_4);
lean_closure_set(x_29, 7, x_5);
lean_closure_set(x_29, 8, x_7);
lean_closure_set(x_29, 9, x_27);
x_30 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_28, x_29);
return x_30;
}
case 4:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_10);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__5), 11, 10);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_8);
lean_closure_set(x_34, 3, x_10);
lean_closure_set(x_34, 4, x_1);
lean_closure_set(x_34, 5, x_3);
lean_closure_set(x_34, 6, x_4);
lean_closure_set(x_34, 7, x_5);
lean_closure_set(x_34, 8, x_7);
lean_closure_set(x_34, 9, x_32);
x_35 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_34);
return x_35;
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
lean_inc(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__6), 11, 10);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_6);
lean_closure_set(x_39, 2, x_8);
lean_closure_set(x_39, 3, x_10);
lean_closure_set(x_39, 4, x_1);
lean_closure_set(x_39, 5, x_3);
lean_closure_set(x_39, 6, x_4);
lean_closure_set(x_39, 7, x_5);
lean_closure_set(x_39, 8, x_7);
lean_closure_set(x_39, 9, x_37);
x_40 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_41, x_10);
lean_inc(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__7), 11, 10);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_6);
lean_closure_set(x_44, 2, x_8);
lean_closure_set(x_44, 3, x_10);
lean_closure_set(x_44, 4, x_1);
lean_closure_set(x_44, 5, x_3);
lean_closure_set(x_44, 6, x_4);
lean_closure_set(x_44, 7, x_5);
lean_closure_set(x_44, 8, x_7);
lean_closure_set(x_44, 9, x_42);
x_45 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_43, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_46, x_10);
lean_inc(x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__8), 11, 10);
lean_closure_set(x_49, 0, x_2);
lean_closure_set(x_49, 1, x_6);
lean_closure_set(x_49, 2, x_8);
lean_closure_set(x_49, 3, x_10);
lean_closure_set(x_49, 4, x_1);
lean_closure_set(x_49, 5, x_3);
lean_closure_set(x_49, 6, x_4);
lean_closure_set(x_49, 7, x_5);
lean_closure_set(x_49, 8, x_7);
lean_closure_set(x_49, 9, x_47);
x_50 = lean_apply_4(x_47, lean_box(0), lean_box(0), x_48, x_49);
return x_50;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_9, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_9, 3);
lean_inc(x_54);
lean_dec(x_9);
x_55 = lean_expr_instantiate_rev(x_52, x_8);
lean_dec(x_52);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_55, x_10);
lean_inc(x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__11___boxed), 14, 13);
lean_closure_set(x_58, 0, x_53);
lean_closure_set(x_58, 1, x_8);
lean_closure_set(x_58, 2, x_1);
lean_closure_set(x_58, 3, x_2);
lean_closure_set(x_58, 4, x_3);
lean_closure_set(x_58, 5, x_4);
lean_closure_set(x_58, 6, x_5);
lean_closure_set(x_58, 7, x_6);
lean_closure_set(x_58, 8, x_7);
lean_closure_set(x_58, 9, x_10);
lean_closure_set(x_58, 10, x_54);
lean_closure_set(x_58, 11, x_51);
lean_closure_set(x_58, 12, x_56);
x_59 = lean_apply_4(x_56, lean_box(0), lean_box(0), x_57, x_58);
return x_59;
}
case 9:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_62 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_60, x_10);
lean_inc(x_61);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__12), 11, 10);
lean_closure_set(x_63, 0, x_2);
lean_closure_set(x_63, 1, x_6);
lean_closure_set(x_63, 2, x_8);
lean_closure_set(x_63, 3, x_10);
lean_closure_set(x_63, 4, x_1);
lean_closure_set(x_63, 5, x_3);
lean_closure_set(x_63, 6, x_4);
lean_closure_set(x_63, 7, x_5);
lean_closure_set(x_63, 8, x_7);
lean_closure_set(x_63, 9, x_61);
x_64 = lean_apply_4(x_61, lean_box(0), lean_box(0), x_62, x_63);
return x_64;
}
case 10:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_67 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_65, x_10);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__13), 11, 10);
lean_closure_set(x_68, 0, x_2);
lean_closure_set(x_68, 1, x_6);
lean_closure_set(x_68, 2, x_8);
lean_closure_set(x_68, 3, x_10);
lean_closure_set(x_68, 4, x_1);
lean_closure_set(x_68, 5, x_3);
lean_closure_set(x_68, 6, x_4);
lean_closure_set(x_68, 7, x_5);
lean_closure_set(x_68, 8, x_7);
lean_closure_set(x_68, 9, x_66);
x_69 = lean_apply_4(x_66, lean_box(0), lean_box(0), x_67, x_68);
return x_69;
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_72 = l_Lean_Meta_transform_visit___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_70, x_10);
lean_inc(x_71);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___rarg___lambda__14), 11, 10);
lean_closure_set(x_73, 0, x_2);
lean_closure_set(x_73, 1, x_6);
lean_closure_set(x_73, 2, x_8);
lean_closure_set(x_73, 3, x_10);
lean_closure_set(x_73, 4, x_1);
lean_closure_set(x_73, 5, x_3);
lean_closure_set(x_73, 6, x_4);
lean_closure_set(x_73, 7, x_5);
lean_closure_set(x_73, 8, x_7);
lean_closure_set(x_73, 9, x_71);
x_74 = lean_apply_4(x_71, lean_box(0), lean_box(0), x_72, x_73);
return x_74;
}
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
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_transform_visit___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__6___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___lambda__2(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitLambda___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__10___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__11___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLambda___spec__12___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_transform_visit_visitLambda___rarg___lambda__9(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__6___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_transform_visit_visitForall___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__10___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__11___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_transform_visit_visitForall___spec__12___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_transform_visit_visitForall___rarg___lambda__9(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__6___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLetDecl___at_Lean_Meta_transform_visit_visitLet___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__10___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__11___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_transform_visit_visitLet___spec__12___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_transform_visit_visitLet___rarg___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_transform_visit___spec__2___rarg___lambda__2___boxed__const__1);
l_Lean_Meta_transform___rarg___closed__1 = _init_l_Lean_Meta_transform___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_transform___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
