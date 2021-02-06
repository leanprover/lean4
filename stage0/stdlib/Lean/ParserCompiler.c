// Lean compiler output
// Module: Lean.ParserCompiler
// Imports: Init Lean.Util.ReplaceExpr Lean.Meta.Basic Lean.Meta.WHNF Lean.ParserCompiler.Attribute Lean.Parser.Extension
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
lean_object* l_Lean_ParserCompiler_replaceParserTy___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__11;
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__3(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__8;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__15;
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_ParserCompiler_compileCategoryParser_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__10;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_addDefaultInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__7;
size_t l_USize_sub(size_t, size_t);
lean_object* l_Lean_ParserCompiler_replaceParserTy(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg(lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser_match__1(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7(lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__4(lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__3(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe___at_Lean_ParserCompiler_compileParserExpr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__2;
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__6;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__5___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_ParserCompiler_compileParserExpr___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1;
extern lean_object* l_Lean_mkSimpleThunk___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__3;
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__6(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__2(lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_ParserCompiler_compileParserExpr___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__5;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__3;
extern lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__3;
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__4;
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__9;
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object*);
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers_match__1(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__5(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_replaceParserTy___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_KeyedDeclsAttribute_init___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
extern lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_min(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe___at_Lean_ParserCompiler_compileParserExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__12;
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object*);
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
return x_4;
}
}
lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_Context_tyName___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_233; lean_object* x_234; size_t x_235; uint8_t x_236; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? x_5 : x_5 % x_2;
x_233 = lean_ctor_get(x_4, 0);
lean_inc(x_233);
x_234 = lean_array_uget(x_233, x_6);
x_235 = lean_ptr_addr(x_234);
lean_dec(x_234);
x_236 = x_235 == x_5;
if (x_236 == 0)
{
uint8_t x_237; 
x_237 = l_Lean_Expr_isOptParam(x_3);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = l_Lean_Parser_evalParserConstUnsafe___closed__1;
x_239 = l_Lean_Expr_isConstOf(x_3, x_238);
if (x_239 == 0)
{
lean_object* x_240; 
lean_dec(x_233);
x_240 = lean_box(0);
x_7 = x_240;
goto block_232;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_241 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_242 = lean_box(0);
x_243 = l_Lean_mkConst(x_241, x_242);
x_244 = lean_array_uset(x_233, x_6, x_3);
x_245 = lean_ctor_get(x_4, 1);
lean_inc(x_245);
lean_dec(x_4);
lean_inc(x_243);
x_246 = lean_array_uset(x_245, x_6, x_243);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_249 = l_Lean_Expr_appFn_x21(x_3);
x_250 = l_Lean_Expr_appArg_x21(x_249);
lean_dec(x_249);
x_251 = l_Lean_Parser_evalParserConstUnsafe___closed__1;
x_252 = l_Lean_Expr_isConstOf(x_250, x_251);
lean_dec(x_250);
if (x_252 == 0)
{
lean_object* x_253; 
lean_dec(x_233);
x_253 = lean_box(0);
x_7 = x_253;
goto block_232;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_254 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_255 = lean_box(0);
x_256 = l_Lean_mkConst(x_254, x_255);
x_257 = lean_array_uset(x_233, x_6, x_3);
x_258 = lean_ctor_get(x_4, 1);
lean_inc(x_258);
lean_dec(x_4);
lean_inc(x_256);
x_259 = lean_array_uset(x_258, x_6, x_256);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_233);
lean_dec(x_3);
x_262 = lean_ctor_get(x_4, 1);
lean_inc(x_262);
x_263 = lean_array_uget(x_262, x_6);
lean_dec(x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_4);
return x_264;
}
block_232:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_8);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_8, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_3);
x_19 = lean_array_uset(x_18, x_6, x_3);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_expr_update_app(x_3, x_12, x_16);
lean_inc(x_24);
x_25 = lean_array_uset(x_23, x_6, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_10);
x_29 = lean_expr_update_app(x_28, x_12, x_16);
lean_inc(x_29);
x_30 = lean_array_uset(x_27, x_6, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_inc(x_3);
x_35 = lean_array_uset(x_34, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(5, 2, 8);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_10);
x_39 = lean_expr_update_app(x_38, x_12, x_32);
lean_inc(x_39);
x_40 = lean_array_uset(x_37, x_6, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 6:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_44);
x_47 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_44, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_45);
x_50 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_45, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_inc(x_3);
x_55 = lean_array_uset(x_54, x_6, x_3);
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_3, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_dec(x_53);
x_61 = (uint8_t)((x_46 << 24) >> 61);
x_62 = lean_expr_update_lambda(x_3, x_61, x_48, x_52);
lean_inc(x_62);
x_63 = lean_array_uset(x_60, x_6, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_50, 1, x_64);
lean_ctor_set(x_50, 0, x_62);
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_3);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_44);
lean_ctor_set(x_66, 2, x_45);
lean_ctor_set_uint64(x_66, sizeof(void*)*3, x_46);
x_67 = (uint8_t)((x_46 << 24) >> 61);
x_68 = lean_expr_update_lambda(x_66, x_67, x_48, x_52);
lean_inc(x_68);
x_69 = lean_array_uset(x_65, x_6, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_50, 1, x_70);
lean_ctor_set(x_50, 0, x_68);
return x_50;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_50, 0);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_50);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_inc(x_3);
x_74 = lean_array_uset(x_73, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_75 = x_3;
} else {
 lean_dec_ref(x_3);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(6, 3, 8);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_43);
lean_ctor_set(x_77, 1, x_44);
lean_ctor_set(x_77, 2, x_45);
lean_ctor_set_uint64(x_77, sizeof(void*)*3, x_46);
x_78 = (uint8_t)((x_46 << 24) >> 61);
x_79 = lean_expr_update_lambda(x_77, x_78, x_48, x_71);
lean_inc(x_79);
x_80 = lean_array_uset(x_76, x_6, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 2);
lean_inc(x_85);
x_86 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_84);
x_87 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_84, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_85);
x_90 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_85, x_89);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_inc(x_3);
x_95 = lean_array_uset(x_94, x_6, x_3);
x_96 = !lean_is_exclusive(x_3);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_3, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_3, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_3, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = (uint8_t)((x_86 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_88, x_92);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_6, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_90, 1, x_104);
lean_ctor_set(x_90, 0, x_102);
return x_90;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
lean_dec(x_93);
x_106 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_106, 0, x_83);
lean_ctor_set(x_106, 1, x_84);
lean_ctor_set(x_106, 2, x_85);
lean_ctor_set_uint64(x_106, sizeof(void*)*3, x_86);
x_107 = (uint8_t)((x_86 << 24) >> 61);
x_108 = lean_expr_update_forall(x_106, x_107, x_88, x_92);
lean_inc(x_108);
x_109 = lean_array_uset(x_105, x_6, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_90, 1, x_110);
lean_ctor_set(x_90, 0, x_108);
return x_90;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_90, 0);
x_112 = lean_ctor_get(x_90, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_90);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_inc(x_3);
x_114 = lean_array_uset(x_113, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_115 = x_3;
} else {
 lean_dec_ref(x_3);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(7, 3, 8);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_83);
lean_ctor_set(x_117, 1, x_84);
lean_ctor_set(x_117, 2, x_85);
lean_ctor_set_uint64(x_117, sizeof(void*)*3, x_86);
x_118 = (uint8_t)((x_86 << 24) >> 61);
x_119 = lean_expr_update_forall(x_117, x_118, x_88, x_111);
lean_inc(x_119);
x_120 = lean_array_uset(x_116, x_6, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
case 8:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint64_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_123 = lean_ctor_get(x_3, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_3, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_3, 3);
lean_inc(x_126);
x_127 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_124);
x_128 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_124, x_4);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_125);
x_131 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_125, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_126);
x_134 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_126, x_133);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_inc(x_3);
x_139 = lean_array_uset(x_138, x_6, x_3);
x_140 = !lean_is_exclusive(x_3);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_3, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_3, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_3, 0);
lean_dec(x_144);
x_145 = lean_ctor_get(x_137, 1);
lean_inc(x_145);
lean_dec(x_137);
x_146 = lean_expr_update_let(x_3, x_129, x_132, x_136);
lean_inc(x_146);
x_147 = lean_array_uset(x_145, x_6, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_134, 1, x_148);
lean_ctor_set(x_134, 0, x_146);
return x_134;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_3);
x_149 = lean_ctor_get(x_137, 1);
lean_inc(x_149);
lean_dec(x_137);
x_150 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_150, 0, x_123);
lean_ctor_set(x_150, 1, x_124);
lean_ctor_set(x_150, 2, x_125);
lean_ctor_set(x_150, 3, x_126);
lean_ctor_set_uint64(x_150, sizeof(void*)*4, x_127);
x_151 = lean_expr_update_let(x_150, x_129, x_132, x_136);
lean_inc(x_151);
x_152 = lean_array_uset(x_149, x_6, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_139);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_134, 1, x_153);
lean_ctor_set(x_134, 0, x_151);
return x_134;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_134, 0);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_134);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_inc(x_3);
x_157 = lean_array_uset(x_156, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_158 = x_3;
} else {
 lean_dec_ref(x_3);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(8, 4, 8);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_123);
lean_ctor_set(x_160, 1, x_124);
lean_ctor_set(x_160, 2, x_125);
lean_ctor_set(x_160, 3, x_126);
lean_ctor_set_uint64(x_160, sizeof(void*)*4, x_127);
x_161 = lean_expr_update_let(x_160, x_129, x_132, x_154);
lean_inc(x_161);
x_162 = lean_array_uset(x_159, x_6, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_157);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
case 10:
{
lean_object* x_165; lean_object* x_166; uint64_t x_167; lean_object* x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_3, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_3, 1);
lean_inc(x_166);
x_167 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_166);
x_168 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_166, x_4);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_inc(x_3);
x_173 = lean_array_uset(x_172, x_6, x_3);
x_174 = !lean_is_exclusive(x_3);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_3, 1);
lean_dec(x_175);
x_176 = lean_ctor_get(x_3, 0);
lean_dec(x_176);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
x_178 = lean_expr_update_mdata(x_3, x_170);
lean_inc(x_178);
x_179 = lean_array_uset(x_177, x_6, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_168, 1, x_180);
lean_ctor_set(x_168, 0, x_178);
return x_168;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_3);
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_dec(x_171);
x_182 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_182, 0, x_165);
lean_ctor_set(x_182, 1, x_166);
lean_ctor_set_uint64(x_182, sizeof(void*)*2, x_167);
x_183 = lean_expr_update_mdata(x_182, x_170);
lean_inc(x_183);
x_184 = lean_array_uset(x_181, x_6, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_173);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_168, 1, x_185);
lean_ctor_set(x_168, 0, x_183);
return x_168;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_ctor_get(x_168, 0);
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_168);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_inc(x_3);
x_189 = lean_array_uset(x_188, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_190 = x_3;
} else {
 lean_dec_ref(x_3);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(10, 2, 8);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_165);
lean_ctor_set(x_192, 1, x_166);
lean_ctor_set_uint64(x_192, sizeof(void*)*2, x_167);
x_193 = lean_expr_update_mdata(x_192, x_186);
lean_inc(x_193);
x_194 = lean_array_uset(x_191, x_6, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
case 11:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_3, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_3, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_3, 2);
lean_inc(x_199);
x_200 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_199);
x_201 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_2, x_199, x_4);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_inc(x_3);
x_206 = lean_array_uset(x_205, x_6, x_3);
x_207 = !lean_is_exclusive(x_3);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_3, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_3, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_3, 0);
lean_dec(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
x_212 = lean_expr_update_proj(x_3, x_203);
lean_inc(x_212);
x_213 = lean_array_uset(x_211, x_6, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_206);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_201, 1, x_214);
lean_ctor_set(x_201, 0, x_212);
return x_201;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_3);
x_215 = lean_ctor_get(x_204, 1);
lean_inc(x_215);
lean_dec(x_204);
x_216 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_216, 0, x_197);
lean_ctor_set(x_216, 1, x_198);
lean_ctor_set(x_216, 2, x_199);
lean_ctor_set_uint64(x_216, sizeof(void*)*3, x_200);
x_217 = lean_expr_update_proj(x_216, x_203);
lean_inc(x_217);
x_218 = lean_array_uset(x_215, x_6, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_206);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_201, 1, x_219);
lean_ctor_set(x_201, 0, x_217);
return x_201;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_220 = lean_ctor_get(x_201, 0);
x_221 = lean_ctor_get(x_201, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_201);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_inc(x_3);
x_223 = lean_array_uset(x_222, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_224 = x_3;
} else {
 lean_dec_ref(x_3);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(11, 3, 8);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_197);
lean_ctor_set(x_226, 1, x_198);
lean_ctor_set(x_226, 2, x_199);
lean_ctor_set_uint64(x_226, sizeof(void*)*3, x_200);
x_227 = lean_expr_update_proj(x_226, x_220);
lean_inc(x_227);
x_228 = lean_array_uset(x_225, x_6, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
default: 
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_3);
lean_ctor_set(x_231, 1, x_4);
return x_231;
}
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_replaceParserTy___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_replaceParserTy(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_replaceParserTy___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_ParserCompiler_replaceParserTy___spec__1___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_replaceParserTy___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_replaceParserTy___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_3, x_1, x_5, x_7);
return x_8;
}
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_5(x_2, x_1, x_9, x_10, x_11, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_1(x_4, x_1);
return x_15;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr_match__6___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_9, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 1;
x_13 = x_3 - x_12;
x_14 = lean_array_uget(x_2, x_13);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_7(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 1;
x_13 = x_3 - x_12;
x_14 = lean_array_uget(x_2, x_13);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_7(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
lean_object* l_Array_foldrMUnsafe___at_Lean_ParserCompiler_compileParserExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_4, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_5, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_16 = lean_usize_of_nat(x_5);
x_17 = l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__3(x_1, x_3, x_15, x_16, x_2, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = lean_nat_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_4);
x_21 = lean_usize_of_nat(x_5);
x_22 = l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__4(x_1, x_3, x_20, x_21, x_2, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_mkApp(x_1, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_nat_dec_le(x_15, x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_7, x_19);
lean_dec(x_7);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_array_get(x_21, x_4, x_8);
x_23 = lean_array_get(x_21, x_5, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = l_Lean_Meta_inferType(x_22, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
x_27 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg(x_25, x_3, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1;
x_31 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_32 = l_Lean_Expr_isConstOf(x_28, x_31);
lean_dec(x_31);
lean_dec(x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_33 = lean_apply_7(x_30, x_9, x_23, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_6, 2);
x_44 = lean_nat_add(x_8, x_43);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_44;
x_9 = x_42;
x_14 = x_41;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
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
lean_object* x_50; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_50 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_1, x_2, x_23, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_53 = lean_apply_7(x_30, x_9, x_51, x_10, x_11, x_12, x_13, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_dec(x_53);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_6, 2);
x_64 = lean_nat_add(x_8, x_63);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_64;
x_9 = x_62;
x_14 = x_61;
goto _start;
}
}
else
{
uint8_t x_66; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
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
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_50);
if (x_70 == 0)
{
return x_50;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_50, 0);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_50);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_27);
if (x_74 == 0)
{
return x_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_27, 0);
x_76 = lean_ctor_get(x_27, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_27);
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
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_24);
if (x_78 == 0)
{
return x_24;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_24, 0);
x_80 = lean_ctor_get(x_24, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_24);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_9);
lean_ctor_set(x_82, 1, x_14);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_9);
lean_ctor_set(x_83, 1, x_14);
return x_83;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___boxed), 14, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_ParserCompiler_compileParserExpr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_nat_dec_le(x_14, x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_6, x_18);
lean_dec(x_6);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_3, x_7);
x_22 = lean_array_get(x_20, x_4, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_inferType(x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg(x_24, x_26, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1;
x_31 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_32 = l_Lean_Expr_isConstOf(x_28, x_31);
lean_dec(x_31);
lean_dec(x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = lean_apply_7(x_30, x_8, x_22, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_5, 2);
x_44 = lean_nat_add(x_7, x_43);
lean_dec(x_7);
x_6 = x_19;
x_7 = x_44;
x_8 = x_42;
x_13 = x_41;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
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
lean_object* x_50; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_50 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_1, x_2, x_22, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_53 = lean_apply_7(x_30, x_8, x_51, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_dec(x_53);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_5, 2);
x_64 = lean_nat_add(x_7, x_63);
lean_dec(x_7);
x_6 = x_19;
x_7 = x_64;
x_8 = x_62;
x_13 = x_61;
goto _start;
}
}
else
{
uint8_t x_66; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
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
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_50);
if (x_70 == 0)
{
return x_50;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_50, 0);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_50);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_27);
if (x_74 == 0)
{
return x_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_27, 0);
x_76 = lean_ctor_get(x_27, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_27);
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
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_23);
if (x_78 == 0)
{
return x_23;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_23, 0);
x_80 = lean_ctor_get(x_23, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_23);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_8);
lean_ctor_set(x_82, 1, x_13);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_8);
lean_ctor_set(x_83, 1, x_13);
return x_83;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkLambdaFVars(x_3, x_11, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint64_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__1___boxed), 9, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_3, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__3(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_inferType(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_ParserCompiler_replaceParserTy___rarg(x_1, x_11);
x_13 = l_Lean_mkSimpleThunk___closed__1;
x_14 = 0;
x_15 = l_Lean_mkForall(x_13, x_14, x_12, x_3);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = l_Lean_ParserCompiler_replaceParserTy___rarg(x_1, x_16);
x_19 = l_Lean_mkSimpleThunk___closed__1;
x_20 = 0;
x_21 = l_Lean_mkForall(x_19, x_20, x_18, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__4___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_foldrMUnsafe___at_Lean_ParserCompiler_compileParserExpr___spec__2(x_9, x_12, x_2, x_13, x_14, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_13);
return x_15;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = lean_array_get_size(x_6);
x_21 = lean_array_get_size(x_19);
x_22 = l_Nat_min(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_17);
x_24 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg(x_2, x_3, x_4, x_6, x_19, x_23, x_22, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_23);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_3);
x_15 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_9, x_2, x_3);
x_16 = l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(x_15, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_18);
x_19 = l_Lean_Meta_inferType(x_18, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(x_7);
x_23 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__6___boxed), 12, 5);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_6);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_8);
lean_closure_set(x_23, 4, x_18);
x_24 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__4___rarg(x_20, x_23, x_10, x_11, x_12, x_13, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_ParserCompiler_replaceParserTy___rarg(x_1, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_17 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_1, x_3, x_16, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__5___boxed), 8, 1);
lean_closure_set(x_20, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_21 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg(x_4, x_20, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
lean_inc(x_5);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
x_26 = lean_box(0);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_24, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_24);
x_37 = lean_st_ref_get(x_14, x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_13, 3);
lean_inc(x_39);
x_40 = l_Lean_MessageData_toString(x_36, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_throwError___at_Lean_ParserCompiler_compileParserExpr___spec__6(x_44, x_11, x_12, x_13, x_14, x_42);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_io_error_to_string(x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_40, 0, x_55);
return x_40;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_40, 0);
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_40);
x_58 = lean_io_error_to_string(x_56);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_39);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_34, 0);
lean_inc(x_63);
lean_dec(x_34);
x_64 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__7(x_6, x_7, x_5, x_24, x_8, x_1, x_3, x_9, x_63, x_11, x_12, x_13, x_14, x_32);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_21);
if (x_65 == 0)
{
return x_21;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_21, 0);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_21);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
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
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_17);
if (x_69 == 0)
{
return x_17;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_17, 0);
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_17);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = lean_array_get_size(x_5);
x_20 = lean_array_get_size(x_18);
x_21 = l_Nat_min(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_16);
x_23 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg(x_2, x_3, x_5, x_18, x_22, x_21, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_22);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("call of unknown parser at '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to generate ");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" for non-definition '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refusing to generate code for imported parser declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'; use `@[runParserAttributeHooks]` on its definition instead.");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" for non-parser combinator '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(x_17, x_15, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_16);
x_19 = l_Lean_Name_append(x_11, x_16);
lean_inc(x_11);
x_20 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_11, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_ConstantInfo_type(x_21);
x_24 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_25 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserExpr___spec__1___rarg(x_23, x_24, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_57; uint8_t x_58; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_57 = l_Lean_Parser_evalParserConstUnsafe___closed__3;
x_58 = l_Lean_Expr_isConstOf(x_26, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Parser_evalParserConstUnsafe___closed__1;
x_60 = l_Lean_Expr_isConstOf(x_26, x_59);
lean_dec(x_26);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_61 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_64, 0, x_16);
x_65 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__12;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_1);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_KernelException_toMessageData___closed__3;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_72, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_16);
lean_dec(x_1);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
lean_dec(x_61);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
lean_dec(x_62);
x_76 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_2, x_3, x_75, x_5, x_6, x_7, x_8, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_61);
if (x_77 == 0)
{
return x_61;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_61, 0);
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_61);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_box(0);
x_28 = x_81;
goto block_56;
}
}
else
{
lean_object* x_82; 
lean_dec(x_26);
x_82 = lean_box(0);
x_28 = x_82;
goto block_56;
}
block_56:
{
lean_object* x_29; 
lean_dec(x_28);
x_29 = l_Lean_ConstantInfo_value_x3f(x_21);
lean_dec(x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_31 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__6;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_KernelException_toMessageData___closed__3;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_38, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = l_Lean_Environment_getModuleIdxFor_x3f(x_15, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8(x_2, x_40, x_3, x_23, x_19, x_17, x_11, x_1, x_24, x_42, x_5, x_6, x_7, x_8, x_27);
return x_43;
}
else
{
lean_dec(x_41);
if (x_3 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_11);
x_45 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__8;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__10;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Meta_addDefaultInstance___spec__1(x_48, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
x_55 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8(x_2, x_40, x_3, x_23, x_19, x_17, x_11, x_1, x_24, x_54, x_5, x_6, x_7, x_8, x_27);
return x_55;
}
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_25);
if (x_83 == 0)
{
return x_25;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_25, 0);
x_85 = lean_ctor_get(x_25, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_25);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_20);
if (x_87 == 0)
{
return x_20;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_20, 0);
x_89 = lean_ctor_get(x_20, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_20);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
x_91 = lean_ctor_get(x_18, 0);
lean_inc(x_91);
lean_dec(x_18);
x_92 = lean_box(0);
x_93 = l_Lean_mkConst(x_91, x_92);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_93);
x_94 = l_Lean_Meta_inferType(x_93, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_box(x_3);
x_98 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__9___boxed), 11, 4);
lean_closure_set(x_98, 0, x_1);
lean_closure_set(x_98, 1, x_2);
lean_closure_set(x_98, 2, x_97);
lean_closure_set(x_98, 3, x_93);
x_99 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__4___rarg(x_95, x_98, x_5, x_6, x_7, x_8, x_96);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_93);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_94);
if (x_100 == 0)
{
return x_94;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_94, 0);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_94);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_10);
lean_dec(x_2);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_1);
x_105 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__2;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_KernelException_toMessageData___closed__3;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_108, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_109;
}
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__3___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__2___boxed), 12, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_box(x_2);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___boxed), 9, 3);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_ParserCompiler_compileParserExpr___rarg___closed__1;
x_17 = l_Lean_ParserCompiler_compileParserExpr_match__6___rarg(x_10, x_13, x_16, x_15);
x_18 = lean_apply_5(x_17, x_4, x_5, x_6, x_7, x_11);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at_Lean_ParserCompiler_compileParserExpr___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_foldrMUnsafe___at_Lean_ParserCompiler_compileParserExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldrMUnsafe___at_Lean_ParserCompiler_compileParserExpr___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Lean_throwError___at_Lean_ParserCompiler_compileParserExpr___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_ParserCompiler_compileParserExpr___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_15 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_10 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__6(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__8(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_17;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__9(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserExpr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileCategoryParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_ParserCompiler_compileCategoryParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileCategoryParser_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserCompiler");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserCompiler.compileCategoryParser");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__2;
x_2 = l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__3;
x_3 = lean_unsigned_to_nat(110u);
x_4 = lean_unsigned_to_nat(6u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = l_Lean_mkConst(x_2, x_7);
x_9 = 0;
x_10 = lean_box(x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_8);
x_12 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_13 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_MetaM_run_x27___rarg(x_11, x_12, x_13, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_mk_syntax_ident(x_2);
x_19 = l_Lean_mkOptionalNode___closed__2;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_nullKind;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
if (x_3 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
x_26 = lean_mk_syntax_ident(x_25);
x_27 = l_Lean_Syntax_mkApp___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_array_push(x_28, x_22);
x_30 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__15;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = 0;
x_33 = l_Lean_Attribute_add(x_17, x_25, x_31, x_32, x_4, x_5, x_16);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_36);
x_37 = lean_mk_syntax_ident(x_36);
x_38 = l_Lean_Syntax_mkApp___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_array_push(x_39, x_22);
x_41 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__15;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = 0;
x_44 = l_Lean_Attribute_add(x_17, x_36, x_42, x_43, x_4, x_5, x_16);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_dec(x_14);
x_46 = l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__1;
x_47 = l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__4;
x_48 = lean_panic_fn(x_46, x_47);
x_49 = lean_apply_3(x_48, x_4, x_5, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileCategoryParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileCategoryParser___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileCategoryParser___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ParserCompiler_compileCategoryParser___rarg(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
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
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_3, x_16, x_17);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_3(x_4, x_19, x_20, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_3(x_6, x_23, x_24, x_25);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_3(x_10, x_27, x_28, x_29);
return x_30;
}
case 5:
{
lean_object* x_31; lean_object* x_32; 
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
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_1(x_11, x_31);
return x_32;
}
case 6:
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
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
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_35 = lean_box(x_34);
x_36 = lean_apply_2(x_12, x_33, x_35);
return x_36;
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_apply_2(x_13, x_37, x_38);
return x_39;
}
case 8:
{
lean_object* x_40; lean_object* x_41; 
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
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_apply_1(x_5, x_40);
return x_41;
}
case 9:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_apply_3(x_7, x_42, x_43, x_44);
return x_45;
}
case 10:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
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
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_50 = lean_box(x_49);
x_51 = lean_apply_4(x_8, x_46, x_47, x_48, x_50);
return x_51;
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
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
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_56 = lean_box(x_55);
x_57 = lean_apply_4(x_9, x_52, x_53, x_54, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileEmbeddedParsers_match__1___rarg), 13, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_2 = x_8;
goto _start;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_ParserCompiler_compileEmbeddedParsers___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
case 3:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
case 4:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = l_Lean_mkConst(x_23, x_24);
x_26 = 0;
x_27 = l_Lean_ParserCompiler_compileParserExpr___rarg(x_1, x_26, x_25, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 9:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_dec(x_2);
x_2 = x_38;
goto _start;
}
case 10:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_ParserCompiler_compileEmbeddedParsers___rarg(x_1, x_40, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_2 = x_41;
x_7 = x_43;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_51 = l_Lean_ParserCompiler_compileEmbeddedParsers___rarg(x_1, x_49, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_2 = x_50;
x_7 = x_52;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileEmbeddedParsers___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
x_12 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__1;
x_13 = l_Lean_Expr_isConstOf(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2;
x_15 = l_Lean_Expr_isConstOf(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Name_isAnonymous(x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_ParserCompiler_compileCategoryParser___rarg(x_1, x_3, x_4, x_5, x_6, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_box(0);
x_19 = l_Lean_mkConst(x_3, x_18);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___rarg___boxed), 8, 3);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_19);
x_23 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_24 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
x_25 = l_Lean_Meta_MetaM_run_x27___rarg(x_22, x_23, x_24, x_5, x_6, x_10);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; 
lean_inc(x_3);
x_36 = l_Lean_evalConstCheck___at_Lean_KeyedDeclsAttribute_init___spec__4___rarg(x_12, x_3, x_5, x_6, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileEmbeddedParsers___rarg), 7, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_41 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
x_42 = l_Lean_Meta_MetaM_run_x27___rarg(x_39, x_40, x_41, x_5, x_6, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = l_Lean_evalConstCheck___at_Lean_KeyedDeclsAttribute_init___spec__4___rarg(x_14, x_3, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileEmbeddedParsers___rarg), 7, 2);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_49 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
x_50 = l_Lean_Meta_MetaM_run_x27___rarg(x_47, x_48, x_49, x_5, x_6, x_46);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_11);
lean_inc(x_3);
x_55 = l_Lean_evalConstCheck___at_Lean_KeyedDeclsAttribute_init___spec__4___rarg(x_12, x_3, x_5, x_6, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileEmbeddedParsers___rarg), 7, 2);
lean_closure_set(x_58, 0, x_1);
lean_closure_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_60 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
x_61 = l_Lean_Meta_MetaM_run_x27___rarg(x_58, x_59, x_60, x_5, x_6, x_57);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2;
x_64 = l_Lean_evalConstCheck___at_Lean_KeyedDeclsAttribute_init___spec__4___rarg(x_63, x_3, x_5, x_6, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileEmbeddedParsers___rarg), 7, 2);
lean_closure_set(x_67, 0, x_1);
lean_closure_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_69 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
x_70 = l_Lean_Meta_MetaM_run_x27___rarg(x_67, x_68, x_69, x_5, x_6, x_66);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_64);
if (x_71 == 0)
{
return x_64;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_64, 0);
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_64);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_8);
if (x_75 == 0)
{
return x_8;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_8, 0);
x_77 = lean_ctor_get(x_8, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_8);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Parser_registerParserAttributeHook(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_WHNF(lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_ParserCompiler(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__5___rarg___closed__1);
l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_ParserCompiler_compileParserExpr___spec__7___rarg___closed__1);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__1 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__1);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__2 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__2);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__3 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__3);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__4);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__5 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__5();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__5);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__6 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__6();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__6);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__7 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__7();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__7);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__8 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__8();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__8);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__9 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__9();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__9);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__10 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__10();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__10);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__11 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__11();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__11);
l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__12 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__12();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___lambda__10___closed__12);
l_Lean_ParserCompiler_compileParserExpr___rarg___closed__1 = _init_l_Lean_ParserCompiler_compileParserExpr___rarg___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserExpr___rarg___closed__1);
l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__1 = _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__1);
l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__2 = _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__2);
l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__3 = _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__3);
l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__4 = _init_l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__4();
lean_mark_persistent(l_Lean_ParserCompiler_compileCategoryParser___rarg___closed__4);
l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__1 = _init_l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__1);
l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2 = _init_l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
