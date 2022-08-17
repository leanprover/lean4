// Lean compiler output
// Module: Lean.Compiler.Simp
// Imports: Init Lean.Compiler.CompilerM Lean.Compiler.Decl Lean.Compiler.Stage1 Lean.Compiler.InlineAttrs
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
lean_object* l_Lean_Compiler_Decl_ensureUniqueLetVarNames(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__5;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__3;
lean_object* l_Lean_Compiler_visitLetImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_Simp_visitLambda___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__4;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__4;
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__1;
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__2;
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getStage1Decl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_Context_localInline___default;
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__2;
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__6;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_JoinPoints_JoinPointChecker_containsNoJp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goLambda___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__4;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__2;
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_InlineStats_format___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3;
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__2;
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__3;
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__5;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__2;
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_attachOptJp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_Simp_InlineStats_format___spec__1(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__5;
static lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__3;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_numOccs___default;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_visitLambda___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__5;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__6;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1;
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__3;
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_shouldInline___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__6;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__2;
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_InlineStats_shouldInline___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Compiler_Simp_instToFormatInlineStats___closed__1;
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getLambdaArity(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__4;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_InlineStats_format___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_size___default;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__1;
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_State_simplified___default;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_InlineStats_format___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats___closed__7;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Decl_simp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_InlineStats_format___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Decl_simp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Decl_simp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_instToFormatInlineStats;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_format(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___closed__7;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goLetValue___spec__46(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_getArity(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Context_config___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkJpDeclIfNotSimple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__2;
static lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__4;
lean_object* l_Lean_Compiler_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goTailApp___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_shouldInline___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__1;
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getLCNFSize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Decl_simp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_InlineStats_shouldInline(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___boxed(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710_(lean_object*);
lean_object* l_Lean_Compiler_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Config_increaseFactor___default;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_JoinPoints_JoinPointChecker_containsNoJp___spec__2(x_6, x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_free_object(x_8);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 4);
lean_inc(x_26);
x_27 = l_Lean_Expr_isLambda(x_26);
if (x_27 == 0)
{
lean_free_object(x_7);
lean_free_object(x_8);
lean_dec(x_16);
x_1 = x_26;
x_5 = x_24;
goto _start;
}
else
{
lean_dec(x_26);
return x_7;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_ctor_get(x_16, 4);
lean_inc(x_30);
x_31 = l_Lean_Expr_isLambda(x_30);
if (x_31 == 0)
{
lean_free_object(x_8);
lean_dec(x_16);
x_1 = x_30;
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_36 = x_7;
} else {
 lean_dec_ref(x_7);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_40 = x_7;
} else {
 lean_dec_ref(x_7);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_34, 4);
lean_inc(x_41);
x_42 = l_Lean_Expr_isLambda(x_41);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_34);
x_1 = x_41;
x_5 = x_39;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_34);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
}
}
}
case 10:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_Simp_findLambda_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_JoinPoints_JoinPointChecker_containsNoJp___spec__2(x_7, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
lean_dec(x_14);
x_21 = 1;
x_1 = x_20;
x_2 = x_21;
x_6 = x_19;
goto _start;
}
}
}
case 10:
{
if (x_2 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = 1;
x_1 = x_24;
x_2 = x_25;
goto _start;
}
}
default: 
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Compiler_Simp_findExpr(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_InlineStats_numOccs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_InlineStats_size___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_InlineStats_format___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_InlineStats_format___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_InlineStats_format___spec__2(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
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
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_Simp_InlineStats_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_InlineStats_format___spec__3(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ↦ ", 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goTailApp___spec__1(x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__2;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_6, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__4;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__6;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Nat_repr(x_7);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__8;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Nat_repr(x_11);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_2 = x_5;
x_3 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_format(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Std_HashMap_toList___at_Lean_Compiler_Simp_InlineStats_format___spec__1(x_2);
x_4 = lean_box(0);
x_5 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_InlineStats_format___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_InlineStats_format___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_InlineStats_format___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_InlineStats_format___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_InlineStats_shouldInline___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goTailApp___spec__1(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_InlineStats_shouldInline(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goTailApp___spec__1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_Simp_InlineStats_shouldInline___lambda__1(x_1, x_2, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_shouldInline___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_Simp_InlineStats_shouldInline___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_InlineStats_shouldInline___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_Simp_InlineStats_shouldInline(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instToFormatInlineStats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_InlineStats_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instToFormatInlineStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_instToFormatInlineStats___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = l_Lean_Compiler_withNewScopeImp___rarg(x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Compiler_Simp_collectInlineStats_go(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_collectInlineStats_goLambda___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_visitLambda___boxed), 5, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Compiler_Simp_collectInlineStats_goLambda___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__2(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(73u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_2 = x_16;
x_3 = x_23;
x_6 = x_24;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_34 = lean_box(0);
x_2 = x_16;
x_3 = x_33;
x_6 = x_34;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_3, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_collectInlineStats_go___lambda__1___boxed), 7, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = l_Lean_Compiler_visitLetImp(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_collectInlineStats_go), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
lean_inc(x_21);
x_25 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1(x_19, x_21, x_22, x_21, x_23, x_24, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 1:
{
lean_object* x_38; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_38 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_44);
x_46 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_45);
x_47 = lean_mk_array(x_45, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_45, x_48);
lean_dec(x_45);
x_50 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_47, x_49);
x_51 = lean_ctor_get(x_43, 3);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 2);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_box(0);
lean_inc(x_52);
x_56 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__2(x_50, x_52, x_53, x_52, x_54, x_55, x_2, x_3, x_4, x_5, x_42);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_50);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_38);
if (x_65 == 0)
{
return x_38;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_38, 0);
x_67 = lean_ctor_get(x_38, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_38);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 2:
{
lean_object* x_69; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_69 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_75);
x_77 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_76);
x_78 = lean_mk_array(x_76, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_76, x_79);
lean_dec(x_76);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_78, x_80);
x_82 = lean_ctor_get(x_74, 3);
lean_inc(x_82);
lean_dec(x_74);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 2);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_box(0);
lean_inc(x_83);
x_87 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__3(x_81, x_83, x_84, x_83, x_85, x_86, x_2, x_3, x_4, x_5, x_73);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_81);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_69);
if (x_96 == 0)
{
return x_69;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_69, 0);
x_98 = lean_ctor_get(x_69, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_69);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
case 3:
{
lean_object* x_100; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_100 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_unsigned_to_nat(0u);
x_107 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_106);
x_108 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_107);
x_109 = lean_mk_array(x_107, x_108);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_sub(x_107, x_110);
lean_dec(x_107);
x_112 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_109, x_111);
x_113 = lean_ctor_get(x_105, 3);
lean_inc(x_113);
lean_dec(x_105);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 2);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_box(0);
lean_inc(x_114);
x_118 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__4(x_112, x_114, x_115, x_114, x_116, x_117, x_2, x_3, x_4, x_5, x_104);
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_112);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_118, 0);
lean_dec(x_120);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_118);
if (x_123 == 0)
{
return x_118;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_118, 0);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_118);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_100);
if (x_127 == 0)
{
return x_100;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_100, 0);
x_129 = lean_ctor_get(x_100, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_100);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
case 4:
{
lean_object* x_131; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_131 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
lean_dec(x_132);
x_137 = lean_unsigned_to_nat(0u);
x_138 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_137);
x_139 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_138);
x_140 = lean_mk_array(x_138, x_139);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_sub(x_138, x_141);
lean_dec(x_138);
x_143 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_140, x_142);
x_144 = lean_ctor_get(x_136, 3);
lean_inc(x_144);
lean_dec(x_136);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 2);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_box(0);
lean_inc(x_145);
x_149 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__5(x_143, x_145, x_146, x_145, x_147, x_148, x_2, x_3, x_4, x_5, x_135);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_149, 0);
lean_dec(x_151);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_149);
if (x_154 == 0)
{
return x_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_149, 0);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_149);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_131);
if (x_158 == 0)
{
return x_131;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_131, 0);
x_160 = lean_ctor_get(x_131, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_131);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
case 5:
{
lean_object* x_162; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_162 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_164);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
lean_dec(x_163);
x_168 = lean_unsigned_to_nat(0u);
x_169 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_168);
x_170 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_169);
x_171 = lean_mk_array(x_169, x_170);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_sub(x_169, x_172);
lean_dec(x_169);
x_174 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_171, x_173);
x_175 = lean_ctor_get(x_167, 3);
lean_inc(x_175);
lean_dec(x_167);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 2);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_box(0);
lean_inc(x_176);
x_180 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__6(x_174, x_176, x_177, x_176, x_178, x_179, x_2, x_3, x_4, x_5, x_166);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_174);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_180, 0);
lean_dec(x_182);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_180);
if (x_185 == 0)
{
return x_180;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_180, 0);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_180);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_162);
if (x_189 == 0)
{
return x_162;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_162, 0);
x_191 = lean_ctor_get(x_162, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_162);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 6:
{
lean_object* x_193; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_193 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
lean_dec(x_193);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
lean_dec(x_194);
x_199 = lean_unsigned_to_nat(0u);
x_200 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_199);
x_201 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_200);
x_202 = lean_mk_array(x_200, x_201);
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_nat_sub(x_200, x_203);
lean_dec(x_200);
x_205 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_202, x_204);
x_206 = lean_ctor_get(x_198, 3);
lean_inc(x_206);
lean_dec(x_198);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 2);
lean_inc(x_209);
lean_dec(x_206);
x_210 = lean_box(0);
lean_inc(x_207);
x_211 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__7(x_205, x_207, x_208, x_207, x_209, x_210, x_2, x_3, x_4, x_5, x_197);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_211, 0);
lean_dec(x_213);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_211);
if (x_216 == 0)
{
return x_211;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_211, 0);
x_218 = lean_ctor_get(x_211, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_211);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_193);
if (x_220 == 0)
{
return x_193;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_193, 0);
x_222 = lean_ctor_get(x_193, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_193);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
case 7:
{
lean_object* x_224; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_224 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_226);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_229 = lean_ctor_get(x_225, 0);
lean_inc(x_229);
lean_dec(x_225);
x_230 = lean_unsigned_to_nat(0u);
x_231 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_230);
x_232 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_231);
x_233 = lean_mk_array(x_231, x_232);
x_234 = lean_unsigned_to_nat(1u);
x_235 = lean_nat_sub(x_231, x_234);
lean_dec(x_231);
x_236 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_233, x_235);
x_237 = lean_ctor_get(x_229, 3);
lean_inc(x_237);
lean_dec(x_229);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 2);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_box(0);
lean_inc(x_238);
x_242 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__8(x_236, x_238, x_239, x_238, x_240, x_241, x_2, x_3, x_4, x_5, x_228);
lean_dec(x_240);
lean_dec(x_238);
lean_dec(x_236);
if (lean_obj_tag(x_242) == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_242, 0);
lean_dec(x_244);
lean_ctor_set(x_242, 0, x_241);
return x_242;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
else
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_242);
if (x_247 == 0)
{
return x_242;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_242, 0);
x_249 = lean_ctor_get(x_242, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_242);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_224);
if (x_251 == 0)
{
return x_224;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_224, 0);
x_253 = lean_ctor_get(x_224, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_224);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
case 8:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_collectInlineStats_go___lambda__2), 6, 1);
lean_closure_set(x_255, 0, x_1);
x_256 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__2;
x_257 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_257, 0, x_255);
lean_closure_set(x_257, 1, x_256);
x_258 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_collectInlineStats_goLambda___spec__2(x_257, x_2, x_3, x_4, x_5, x_6);
return x_258;
}
case 9:
{
lean_object* x_259; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_259 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_261);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
lean_dec(x_259);
x_264 = lean_ctor_get(x_260, 0);
lean_inc(x_264);
lean_dec(x_260);
x_265 = lean_unsigned_to_nat(0u);
x_266 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_265);
x_267 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_266);
x_268 = lean_mk_array(x_266, x_267);
x_269 = lean_unsigned_to_nat(1u);
x_270 = lean_nat_sub(x_266, x_269);
lean_dec(x_266);
x_271 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_268, x_270);
x_272 = lean_ctor_get(x_264, 3);
lean_inc(x_272);
lean_dec(x_264);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 2);
lean_inc(x_275);
lean_dec(x_272);
x_276 = lean_box(0);
lean_inc(x_273);
x_277 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__9(x_271, x_273, x_274, x_273, x_275, x_276, x_2, x_3, x_4, x_5, x_263);
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_271);
if (lean_obj_tag(x_277) == 0)
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_277, 0);
lean_dec(x_279);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
lean_dec(x_277);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
else
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_277);
if (x_282 == 0)
{
return x_277;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_277, 0);
x_284 = lean_ctor_get(x_277, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_277);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_259);
if (x_286 == 0)
{
return x_259;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_259, 0);
x_288 = lean_ctor_get(x_259, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_259);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
case 10:
{
lean_object* x_290; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_290 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_292);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
lean_dec(x_290);
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_unsigned_to_nat(0u);
x_297 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_296);
x_298 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_297);
x_299 = lean_mk_array(x_297, x_298);
x_300 = lean_unsigned_to_nat(1u);
x_301 = lean_nat_sub(x_297, x_300);
lean_dec(x_297);
x_302 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_299, x_301);
x_303 = lean_ctor_get(x_295, 3);
lean_inc(x_303);
lean_dec(x_295);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 2);
lean_inc(x_306);
lean_dec(x_303);
x_307 = lean_box(0);
lean_inc(x_304);
x_308 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__10(x_302, x_304, x_305, x_304, x_306, x_307, x_2, x_3, x_4, x_5, x_294);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_302);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; 
x_310 = lean_ctor_get(x_308, 0);
lean_dec(x_310);
lean_ctor_set(x_308, 0, x_307);
return x_308;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
else
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_308);
if (x_313 == 0)
{
return x_308;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_308, 0);
x_315 = lean_ctor_get(x_308, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_308);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
}
else
{
uint8_t x_317; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_317 = !lean_is_exclusive(x_290);
if (x_317 == 0)
{
return x_290;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_290, 0);
x_319 = lean_ctor_get(x_290, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_290);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
}
default: 
{
lean_object* x_321; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_321 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = l_Lean_Compiler_Simp_collectInlineStats_goValue(x_1, x_2, x_3, x_4, x_5, x_323);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_dec(x_321);
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
lean_dec(x_322);
x_327 = lean_unsigned_to_nat(0u);
x_328 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_327);
x_329 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_328);
x_330 = lean_mk_array(x_328, x_329);
x_331 = lean_unsigned_to_nat(1u);
x_332 = lean_nat_sub(x_328, x_331);
lean_dec(x_328);
x_333 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_330, x_332);
x_334 = lean_ctor_get(x_326, 3);
lean_inc(x_334);
lean_dec(x_326);
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_334, 2);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_box(0);
lean_inc(x_335);
x_339 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__11(x_333, x_335, x_336, x_335, x_337, x_338, x_2, x_3, x_4, x_5, x_325);
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_333);
if (lean_obj_tag(x_339) == 0)
{
uint8_t x_340; 
x_340 = !lean_is_exclusive(x_339);
if (x_340 == 0)
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_339, 0);
lean_dec(x_341);
lean_ctor_set(x_339, 0, x_338);
return x_339;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
else
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_339);
if (x_344 == 0)
{
return x_339;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_339, 0);
x_346 = lean_ctor_get(x_339, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_339);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_321);
if (x_348 == 0)
{
return x_321;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_321, 0);
x_350 = lean_ctor_get(x_321, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_321);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_4, 2);
x_14 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_16, x_18, x_1);
lean_dec(x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__3;
x_3 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__4;
x_4 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_st_ref_take(x_6, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_29 = 0;
x_30 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_PersistentArray_push___rarg(x_27, x_31);
lean_ctor_set(x_24, 3, x_32);
x_33 = lean_st_ref_set(x_6, x_24, x_25);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 4);
x_45 = lean_ctor_get(x_24, 5);
x_46 = lean_ctor_get(x_24, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_47 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_48 = 0;
x_49 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_22);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
lean_inc(x_8);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_43, x_50);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_42);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_46);
x_53 = lean_st_ref_set(x_6, x_52, x_25);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_LocalDecl_value(x_1);
x_9 = l_Lean_Expr_isLambda(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_LocalDecl_userName(x_1);
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goTailApp___spec__1(x_18, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_inc(x_6);
x_20 = l_Lean_Compiler_getLCNFSize(x_8, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_6, x_22);
lean_dec(x_6);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_3, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_32 = l_Std_HashMap_insert___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goLetValue___spec__46(x_29, x_12, x_31);
x_33 = l_Std_HashMap_insert___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goLetValue___spec__46(x_30, x_12, x_21);
lean_ctor_set(x_26, 1, x_33);
lean_ctor_set(x_26, 0, x_32);
x_34 = lean_st_ref_set(x_3, x_26, x_27);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_44 = l_Std_HashMap_insert___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goLetValue___spec__46(x_41, x_12, x_43);
x_45 = l_Std_HashMap_insert___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goLetValue___spec__46(x_42, x_12, x_21);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_st_ref_set(x_3, x_46, x_27);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_5);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
lean_dec(x_19);
x_57 = lean_st_ref_get(x_6, x_17);
lean_dec(x_6);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_3, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_56, x_63);
lean_dec(x_56);
x_65 = l_Std_HashMap_insert___at_Lean_Compiler_JoinPoints_JoinPointFinder_findJoinPoints_goLetValue___spec__46(x_62, x_12, x_64);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_st_ref_set(x_3, x_67, x_61);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("debug", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__2;
x_2 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("found decl ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_8 = l_Lean_Compiler_Simp_findLambda_x3f(x_7, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__4;
x_19 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1(x_18, x_2, x_3, x_4, x_5, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1(x_17, x_23, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_17);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = l_Lean_LocalDecl_userName(x_17);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__6;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2(x_18, x_31, x_2, x_3, x_4, x_5, x_25);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1(x_17, x_33, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_33);
lean_dec(x_17);
return x_35;
}
}
}
case 6:
{
lean_object* x_36; 
x_36 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_1, x_2, x_3, x_4, x_5, x_6);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_collectInlineStats_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_collectInlineStats_goValue___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Simp_collectInlineStats___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_Simp_collectInlineStats___closed__4;
x_3 = l_Lean_Compiler_Simp_collectInlineStats___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_collectInlineStats___closed__2;
x_2 = l_Lean_Compiler_Simp_collectInlineStats___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_collectInlineStats___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_Simp_collectInlineStats___closed__6;
x_2 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_collectInlineStats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_Simp_collectInlineStats___closed__7;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_Simp_collectInlineStats___closed__1;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_15);
x_17 = l_Lean_Compiler_Simp_collectInlineStats_goLambda(x_1, x_15, x_9, x_2, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_3, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_3, x_23);
lean_dec(x_3);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_9, x_25);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_Config_increaseFactor___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_Context_config___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_Simp_Context_localInline___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_Simp_State_simplified___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_st_ref_set(x_1, x_11, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_markSimplified___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_Simp_markSimplified___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_Simp_markSimplified(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_LocalDecl_userName(x_1);
x_14 = l_Lean_Compiler_Simp_InlineStats_shouldInline(x_12, x_13);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_shouldInline(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = lean_nat_sub(x_11, x_2);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_9);
x_11 = lean_nat_dec_lt(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_LocalDecl_value(x_1);
x_11 = l_Lean_Compiler_getLambdaArity(x_10);
lean_dec(x_10);
x_12 = lean_apply_7(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Compiler_getStage1Decl_x3f(x_1, x_7, x_8, x_9);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_Compiler_Decl_getArity(x_19);
lean_dec(x_19);
x_21 = lean_apply_7(x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_getAppFn(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
lean_inc(x_10);
x_17 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_15, x_16, x_10);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_11);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(x_10, x_9, x_19, x_2, x_3, x_4, x_5, x_6, x_14);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
lean_inc(x_10);
x_25 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_23, x_24, x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(x_10, x_9, x_28, x_2, x_3, x_4, x_5, x_6, x_22);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Compiler_Simp_findLambda_x3f(x_8, x_4, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
lean_inc(x_2);
x_40 = l_Lean_Compiler_Simp_shouldInline(x_39, x_2, x_3, x_4, x_5, x_6, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_box(0);
x_51 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(x_39, x_9, x_50, x_2, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_39);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_10 = 1;
lean_inc(x_1);
x_11 = l_Lean_Compiler_Simp_findExpr(x_1, x_10, x_4, x_5, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_isLambda(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_1, x_13);
lean_dec(x_1);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
x_17 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
return x_11;
}
}
else
{
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = l_Lean_Expr_isLambda(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_eqv(x_1, x_22);
lean_dec(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_expandTrivialExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_visitLambda___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_1, x_2, x_3);
x_9 = l_Lean_Compiler_withNewScopeImp___rarg(x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_visitLambda(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Compiler_Simp_visitLet(x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_mkLetUsingScope(x_12, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_mkLambda(x_8, x_15, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_visitLambda___lambda__2), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_visitLambda___lambda__1___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Compiler_Simp_visitLambda___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_visitLambda___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l_Lean_Expr_isFVar(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_6);
x_16 = l_Lean_Compiler_Simp_inlineApp_x3f(x_6, x_2, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_expr_instantiate_rev(x_3, x_2);
lean_dec(x_3);
x_20 = l_Lean_Compiler_mkLetDecl(x_4, x_19, x_6, x_5, x_10, x_11, x_12, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_2, x_21);
x_24 = l_Lean_Compiler_Simp_visitLet(x_1, x_23, x_8, x_9, x_10, x_11, x_12, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
lean_dec(x_3);
x_35 = l_Lean_Compiler_Simp_markSimplified___rarg(x_9, x_10, x_11, x_12, x_13);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_array_push(x_2, x_6);
x_38 = l_Lean_Compiler_Simp_visitLet(x_1, x_37, x_8, x_9, x_10, x_11, x_12, x_36);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_14 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_15 = l_Lean_Expr_isLambda(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_12, x_2, x_10, x_9, x_13, x_14, x_16, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Compiler_Simp_visitLambda(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_12, x_2, x_10, x_9, x_13, x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_28 = l_Lean_Compiler_isCasesApp_x3f(x_27, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_27);
x_33 = l_Lean_Compiler_Simp_inlineApp_x3f(x_27, x_32, x_31, x_3, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Compiler_Simp_expandTrivialExpr(x_27, x_3, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_Lean_Compiler_Simp_visitCases(x_48, x_27, x_3, x_4, x_5, x_6, x_7, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_array_fget(x_5, x_2);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_5, x_2, x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Compiler_Simp_visitLambda(x_21, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_fset(x_23, x_2, x_25);
x_28 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_28;
x_5 = x_27;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__4;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!alt.isLambda\n    ", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__1;
x_2 = l_Lean_Compiler_Simp_visitCases___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp.visitCases", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__4;
x_2 = l_Lean_Compiler_Simp_visitCases___closed__5;
x_3 = lean_unsigned_to_nat(179u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_Simp_visitCases___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_9);
x_11 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_sub(x_17, x_13);
lean_dec(x_17);
x_19 = lean_array_get_size(x_15);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_18);
x_81 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_82 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_81);
x_21 = x_82;
goto block_80;
}
else
{
lean_object* x_83; 
x_83 = lean_array_fget(x_15, x_18);
lean_dec(x_18);
x_21 = x_83;
goto block_80;
}
block_80:
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = 1;
x_23 = l_Lean_Compiler_Simp_findExpr(x_21, x_22, x_5, x_6, x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_7, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_constructorApp_x3f(x_29, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_19);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_32);
x_35 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(x_32, x_33, x_32, x_34, x_15, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_34);
lean_dec(x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_39 = l_Lean_mkAppN(x_38, x_37);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_43 = l_Lean_mkAppN(x_42, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_nat_add(x_54, x_52);
lean_dec(x_52);
lean_dec(x_54);
x_56 = lean_nat_dec_lt(x_55, x_19);
lean_dec(x_19);
x_57 = lean_ctor_get(x_50, 3);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_array_get_size(x_51);
x_59 = l_Array_toSubarray___rarg(x_51, x_57, x_58);
x_60 = l_Array_ofSubarray___rarg(x_59);
if (x_56 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_55);
lean_dec(x_15);
x_61 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4;
x_62 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_61);
x_63 = l_Lean_Expr_beta(x_62, x_60);
x_64 = l_Lean_Expr_isLambda(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = l_Lean_Compiler_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_28);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_68 = l_Lean_Compiler_Simp_visitLet(x_63, x_67, x_3, x_4, x_5, x_6, x_7, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
x_69 = l_Lean_Compiler_Simp_visitCases___closed__6;
x_70 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_69, x_3, x_4, x_5, x_6, x_7, x_28);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_array_fget(x_15, x_55);
lean_dec(x_55);
lean_dec(x_15);
x_72 = l_Lean_Expr_beta(x_71, x_60);
x_73 = l_Lean_Expr_isLambda(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Lean_Compiler_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_28);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_77 = l_Lean_Compiler_Simp_visitLet(x_72, x_76, x_3, x_4, x_5, x_6, x_7, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_72);
x_78 = l_Lean_Compiler_Simp_visitCases___closed__6;
x_79 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_78, x_3, x_4, x_5, x_6, x_7, x_28);
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Compiler_mkLocalDecl(x_1, x_2, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_mkLetUsingScope(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___closed__1;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Lean_Compiler_mkLambda(x_13, x_10, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__3;
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__4;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
lean_dec(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_get_size(x_2);
x_16 = l_Array_toSubarray___rarg(x_2, x_3, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
lean_inc(x_6);
x_18 = l_Lean_mkAppN(x_6, x_17);
x_19 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_11);
lean_inc(x_10);
x_20 = l_Lean_Compiler_mkAuxLetDecl(x_18, x_19, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = lean_array_push(x_5, x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Compiler_Simp_visitLet(x_21, x_23, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_6, x_25, x_7, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_8);
lean_dec(x_7);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_array_push(x_5, x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Compiler_Simp_visitLet(x_34, x_35, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_6, x_37, x_7, x_8, x_9, x_10, x_11, x_38);
lean_dec(x_8);
lean_dec(x_7);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_6);
x_48 = lean_array_push(x_5, x_6);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__6;
x_50 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_49);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_51 = l_Lean_Compiler_Simp_visitLet(x_50, x_48, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_6, x_52, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_8);
lean_dec(x_7);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_59);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = l_Lean_Compiler_Simp_visitLet(x_59, x_48, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_6, x_61, x_7, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_8);
lean_dec(x_7);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_y", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_5);
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
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_20 = x_11;
} else {
 lean_dec_ref(x_11);
 x_20 = lean_box(0);
}
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_21);
x_23 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
lean_inc(x_1);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_24, x_26);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_83; 
x_83 = lean_nat_dec_eq(x_19, x_21);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
x_28 = x_84;
goto block_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
x_85 = lean_box(0);
x_86 = l_Lean_Compiler_Simp_inlineApp(x_1, x_85, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_86, 0, x_89);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
x_28 = x_98;
goto block_82;
}
block_82:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_29 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_30 = lean_array_get_size(x_27);
x_31 = lean_nat_sub(x_30, x_19);
lean_dec(x_30);
lean_inc(x_31);
lean_inc(x_27);
x_32 = l_Array_toSubarray___rarg(x_27, x_21, x_31);
x_33 = l_Array_ofSubarray___rarg(x_32);
x_34 = l_Lean_mkAppN(x_29, x_33);
x_35 = lean_st_ref_get(x_8, x_18);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_6, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_41 = l_Lean_Compiler_InferType_inferType(x_34, x_40, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__2;
x_45 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_44, x_7, x_8, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_48, 0, x_46);
lean_closure_set(x_48, 1, x_42);
x_49 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3), 12, 5);
lean_closure_set(x_49, 0, x_19);
lean_closure_set(x_49, 1, x_27);
lean_closure_set(x_49, 2, x_31);
lean_closure_set(x_49, 3, x_3);
lean_closure_set(x_49, 4, x_2);
x_50 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_Simp_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_Simp_visitLambda___spec__2(x_50, x_4, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_8);
lean_inc(x_7);
x_54 = l_Lean_Compiler_mkJpDeclIfNotSimple(x_52, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
if (lean_is_scalar(x_20)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_20;
}
lean_ctor_set(x_57, 0, x_55);
x_58 = l_Lean_Compiler_Simp_inlineApp(x_34, x_57, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_54);
if (x_70 == 0)
{
return x_54;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_54, 0);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_54);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_51);
if (x_74 == 0)
{
return x_51;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_51, 0);
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_51);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_41);
if (x_78 == 0)
{
return x_41;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_41, 0);
x_80 = lean_ctor_get(x_41, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_41);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_10);
if (x_99 == 0)
{
return x_10;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_10, 0);
x_101 = lean_ctor_get(x_10, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_10);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_7, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 2);
x_21 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6;
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_st_ref_take(x_7, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 3);
x_29 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_30 = 0;
x_31 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
lean_inc(x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_28, x_32);
lean_ctor_set(x_25, 3, x_33);
x_34 = lean_st_ref_set(x_7, x_25, x_26);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
x_47 = lean_ctor_get(x_25, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_48 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_49 = 0;
x_50 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_23);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_inc(x_9);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_44, x_51);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_46);
lean_ctor_set(x_53, 6, x_47);
x_54 = lean_st_ref_set(x_7, x_53, x_26);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!value.isLambda\n  ", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__1;
x_2 = l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp.inlineApp", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__4;
x_2 = l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3;
x_3 = lean_unsigned_to_nat(200u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Compiler_Simp_collectInlineStats_go___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Lean_Expr_beta(x_4, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_Compiler_attachOptJp(x_18, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_isLambda(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Compiler_Simp_markSimplified___rarg(x_6, x_7, x_8, x_9, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_isConst(x_3);
lean_dec(x_3);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_27);
x_28 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_29 = l_Lean_Compiler_Simp_visitLet(x_20, x_28, x_5, x_6, x_7, x_8, x_9, x_24);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 0;
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_30);
x_31 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_32 = l_Lean_Compiler_Simp_visitLet(x_20, x_31, x_5, x_6, x_7, x_8, x_9, x_24);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = l_Lean_Expr_isConst(x_3);
lean_dec(x_3);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 1;
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_36);
x_38 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_39 = l_Lean_Compiler_Simp_visitLet(x_20, x_38, x_37, x_6, x_7, x_8, x_9, x_24);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_40);
x_42 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_43 = l_Lean_Compiler_Simp_visitLet(x_20, x_42, x_41, x_6, x_7, x_8, x_9, x_24);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_20);
lean_dec(x_3);
x_44 = l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__4;
x_45 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_44, x_5, x_6, x_7, x_8, x_9, x_21);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__4;
x_2 = l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3;
x_3 = lean_unsigned_to_nat(195u);
x_4 = lean_unsigned_to_nat(43u);
x_5 = l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__4;
x_2 = l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3;
x_3 = lean_unsigned_to_nat(192u);
x_4 = lean_unsigned_to_nat(48u);
x_5 = l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Compiler_getStage1Decl_x3f(x_11, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_16, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_Simp_inlineApp___lambda__1(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_28, x_12, x_27);
lean_dec(x_12);
lean_dec(x_28);
x_30 = l_Lean_Compiler_Simp_inlineApp___lambda__1(x_1, x_2, x_3, x_29, x_5, x_6, x_7, x_8, x_9, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_3);
x_35 = l_Lean_Compiler_Simp_findLambda_x3f(x_3, x_7, x_8, x_9, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_38, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_Simp_inlineApp___lambda__1(x_1, x_2, x_3, x_40, x_5, x_6, x_7, x_8, x_9, x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
x_49 = l_Lean_LocalDecl_value(x_48);
lean_dec(x_48);
x_50 = l_Lean_Compiler_Simp_inlineApp___lambda__1(x_1, x_2, x_3, x_49, x_5, x_6, x_7, x_8, x_9, x_47);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_inlineApp___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp___closed__2;
x_2 = l_Lean_Compiler_Simp_inlineApp___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inline", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp___closed__4;
x_2 = l_Lean_Compiler_Simp_inlineApp___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inlining ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Simp_inlineApp___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Expr_getAppFn(x_1);
x_10 = l_Lean_Compiler_Simp_inlineApp___closed__6;
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp___spec__1(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_Simp_inlineApp___lambda__2(x_1, x_2, x_9, x_15, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_1);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_1);
x_19 = l_Lean_Compiler_Simp_inlineApp___closed__8;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp___spec__2(x_10, x_22, x_3, x_4, x_5, x_6, x_7, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_Simp_inlineApp___lambda__2(x_1, x_2, x_9, x_24, x_3, x_4, x_5, x_6, x_7, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_visitLambda___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Decl_simp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_2, 2);
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_2, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_16, x_1);
lean_dec(x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Decl_simp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_16 = 0;
x_17 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_16);
lean_inc(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Std_PersistentArray_push___rarg(x_14, x_18);
lean_ctor_set(x_11, 3, x_19);
x_20 = lean_st_ref_set(x_4, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get(x_11, 4);
x_32 = lean_ctor_get(x_11, 5);
x_33 = lean_ctor_get(x_11, 6);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_34 = l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7;
x_35 = 0;
x_36 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_8);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_35);
lean_inc(x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_PersistentArray_push___rarg(x_30, x_37);
x_39 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_31);
lean_ctor_set(x_39, 5, x_32);
lean_ctor_set(x_39, 6, x_33);
x_40 = lean_st_ref_set(x_4, x_39, x_12);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_Simp_collectInlineStats___closed__7;
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_st_mk_ref(x_22, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_24);
x_26 = l_Lean_Compiler_Simp_visitLambda(x_2, x_12, x_24, x_17, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_8, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_24, x_30);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_8, x_33);
lean_dec(x_8);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_17, x_35);
lean_dec(x_17);
x_37 = lean_unbox(x_32);
lean_dec(x_32);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_36, 0);
lean_dec(x_45);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 2, x_5);
lean_ctor_set(x_46, 3, x_27);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_36, 0, x_47);
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_4);
lean_ctor_set(x_49, 2, x_5);
lean_ctor_set(x_49, 3, x_27);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
return x_26;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_26);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stats", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp___closed__6;
x_2 = l_Lean_Compiler_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Decl_simp_x3f___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Compiler_Decl_ensureUniqueLetVarNames(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 3);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Compiler_Simp_collectInlineStats(x_11, x_2, x_3, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_Decl_simp_x3f___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Decl_simp_x3f___spec__1(x_15, x_2, x_3, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_Decl_simp_x3f___lambda__1(x_13, x_11, x_8, x_9, x_10, x_20, x_2, x_3, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_8);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_8);
x_24 = l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Compiler_Decl_simp_x3f___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_13);
x_28 = l_Lean_Compiler_Simp_InlineStats_format(x_13);
x_29 = l_Lean_Compiler_Decl_simp_x3f___closed__5;
x_30 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
x_34 = l_Lean_addTrace___at_Lean_Compiler_Decl_simp_x3f___spec__2(x_15, x_33, x_2, x_3, x_22);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Compiler_Decl_simp_x3f___lambda__1(x_13, x_11, x_8, x_9, x_10, x_35, x_2, x_3, x_36);
lean_dec(x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
return x_5;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Decl_simp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Decl_simp_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Decl_simp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_Compiler_Decl_simp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Decl_simp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Compiler_Decl_simp_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_1 = x_12;
x_4 = x_11;
goto _start;
}
}
else
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp___closed__4;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_Simp_inlineApp___closed__6;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__2;
x_7 = l_Lean_registerTraceClass(x_6, x_3, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_Decl_simp_x3f___closed__2;
x_10 = l_Lean_registerTraceClass(x_9, x_3, x_8);
return x_10;
}
else
{
uint8_t x_11; 
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
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Stage1(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Decl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Stage1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1 = _init_l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_InlineStats_numOccs___default___closed__1);
l_Lean_Compiler_Simp_InlineStats_numOccs___default = _init_l_Lean_Compiler_Simp_InlineStats_numOccs___default();
lean_mark_persistent(l_Lean_Compiler_Simp_InlineStats_numOccs___default);
l_Lean_Compiler_Simp_InlineStats_size___default = _init_l_Lean_Compiler_Simp_InlineStats_size___default();
lean_mark_persistent(l_Lean_Compiler_Simp_InlineStats_size___default);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__1 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__1);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__2 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__2);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__3);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__4 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__4);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__5 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__5);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__6 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__6();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__6);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__7 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__7();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__7);
l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__8 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__8();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_InlineStats_format___spec__4___closed__8);
l_Lean_Compiler_Simp_instToFormatInlineStats___closed__1 = _init_l_Lean_Compiler_Simp_instToFormatInlineStats___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_instToFormatInlineStats___closed__1);
l_Lean_Compiler_Simp_instToFormatInlineStats = _init_l_Lean_Compiler_Simp_instToFormatInlineStats();
lean_mark_persistent(l_Lean_Compiler_Simp_instToFormatInlineStats);
l_Lean_Compiler_Simp_collectInlineStats_goLambda___closed__1 = _init_l_Lean_Compiler_Simp_collectInlineStats_goLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goLambda___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__3);
l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_collectInlineStats_go___spec__1___closed__4);
l_Lean_Compiler_Simp_collectInlineStats_go___closed__1 = _init_l_Lean_Compiler_Simp_collectInlineStats_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_go___closed__1);
l_Lean_Compiler_Simp_collectInlineStats_go___closed__2 = _init_l_Lean_Compiler_Simp_collectInlineStats_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_go___closed__2);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__2);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__3);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__4 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__4);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__5 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__5);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__6);
l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7 = _init_l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_Simp_collectInlineStats_goValue___spec__2___closed__7);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__1 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__1);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__2 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__2);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__3 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__3);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__4 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__4);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__5 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__5);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__6 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__6);
l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7 = _init_l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats_goValue___closed__7);
l_Lean_Compiler_Simp_collectInlineStats___closed__1 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__1);
l_Lean_Compiler_Simp_collectInlineStats___closed__2 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__2);
l_Lean_Compiler_Simp_collectInlineStats___closed__3 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__3);
l_Lean_Compiler_Simp_collectInlineStats___closed__4 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__4);
l_Lean_Compiler_Simp_collectInlineStats___closed__5 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__5);
l_Lean_Compiler_Simp_collectInlineStats___closed__6 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__6);
l_Lean_Compiler_Simp_collectInlineStats___closed__7 = _init_l_Lean_Compiler_Simp_collectInlineStats___closed__7();
lean_mark_persistent(l_Lean_Compiler_Simp_collectInlineStats___closed__7);
l_Lean_Compiler_Simp_Config_increaseFactor___default = _init_l_Lean_Compiler_Simp_Config_increaseFactor___default();
lean_mark_persistent(l_Lean_Compiler_Simp_Config_increaseFactor___default);
l_Lean_Compiler_Simp_Context_config___default = _init_l_Lean_Compiler_Simp_Context_config___default();
lean_mark_persistent(l_Lean_Compiler_Simp_Context_config___default);
l_Lean_Compiler_Simp_Context_localInline___default = _init_l_Lean_Compiler_Simp_Context_localInline___default();
l_Lean_Compiler_Simp_State_simplified___default = _init_l_Lean_Compiler_Simp_State_simplified___default();
l_Lean_Compiler_Simp_visitLambda___closed__1 = _init_l_Lean_Compiler_Simp_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_visitLambda___closed__1);
l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1 = _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1);
l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2 = _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2);
l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__3 = _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__3);
l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__4 = _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__4);
l_Lean_Compiler_Simp_visitCases___closed__1 = _init_l_Lean_Compiler_Simp_visitCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__1);
l_Lean_Compiler_Simp_visitCases___closed__2 = _init_l_Lean_Compiler_Simp_visitCases___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__2);
l_Lean_Compiler_Simp_visitCases___closed__3 = _init_l_Lean_Compiler_Simp_visitCases___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__3);
l_Lean_Compiler_Simp_visitCases___closed__4 = _init_l_Lean_Compiler_Simp_visitCases___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__4);
l_Lean_Compiler_Simp_visitCases___closed__5 = _init_l_Lean_Compiler_Simp_visitCases___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__5);
l_Lean_Compiler_Simp_visitCases___closed__6 = _init_l_Lean_Compiler_Simp_visitCases___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__6);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__3 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__3);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__4 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__4);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__5 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__5);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__6 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__6);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__2);
l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__1);
l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__2);
l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__3);
l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__4 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__1___closed__4);
l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__1);
l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__2);
l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__3 = _init_l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___lambda__2___closed__3);
l_Lean_Compiler_Simp_inlineApp___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__1);
l_Lean_Compiler_Simp_inlineApp___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__2);
l_Lean_Compiler_Simp_inlineApp___closed__3 = _init_l_Lean_Compiler_Simp_inlineApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__3);
l_Lean_Compiler_Simp_inlineApp___closed__4 = _init_l_Lean_Compiler_Simp_inlineApp___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__4);
l_Lean_Compiler_Simp_inlineApp___closed__5 = _init_l_Lean_Compiler_Simp_inlineApp___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__5);
l_Lean_Compiler_Simp_inlineApp___closed__6 = _init_l_Lean_Compiler_Simp_inlineApp___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__6);
l_Lean_Compiler_Simp_inlineApp___closed__7 = _init_l_Lean_Compiler_Simp_inlineApp___closed__7();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__7);
l_Lean_Compiler_Simp_inlineApp___closed__8 = _init_l_Lean_Compiler_Simp_inlineApp___closed__8();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp___closed__8);
l_Lean_Compiler_Decl_simp_x3f___closed__1 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__1);
l_Lean_Compiler_Decl_simp_x3f___closed__2 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__2);
l_Lean_Compiler_Decl_simp_x3f___closed__3 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__3);
l_Lean_Compiler_Decl_simp_x3f___closed__4 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__4);
l_Lean_Compiler_Decl_simp_x3f___closed__5 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__5();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__5);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710____closed__2);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_3710_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
