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
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser(lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_State_inhabited___closed__7;
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAttribute(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__2;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_Table_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main(lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___main___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_mkInitAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_inhabited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_mkAppStx___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = x_9 == x_5;
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_12 = l_Lean_Expr_isConstOf(x_3, x_11);
if (x_12 == 0)
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_13, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_14, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_3);
x_23 = lean_array_uset(x_22, x_6, x_3);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_expr_update_app(x_3, x_16, x_20);
lean_inc(x_25);
x_26 = lean_array_uset(x_24, x_6, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_inc(x_3);
x_31 = lean_array_uset(x_30, x_6, x_3);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_expr_update_app(x_3, x_16, x_28);
lean_inc(x_33);
x_34 = lean_array_uset(x_32, x_6, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
case 6:
{
lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_40 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_37, x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_38, x_42);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_inc(x_3);
x_48 = lean_array_uset(x_47, x_6, x_3);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = (uint8_t)((x_39 << 24) >> 61);
x_51 = lean_expr_update_lambda(x_3, x_50, x_41, x_45);
lean_inc(x_51);
x_52 = lean_array_uset(x_49, x_6, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_43, 1, x_53);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_inc(x_3);
x_57 = lean_array_uset(x_56, x_6, x_3);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = (uint8_t)((x_39 << 24) >> 61);
x_60 = lean_expr_update_lambda(x_3, x_59, x_41, x_54);
lean_inc(x_60);
x_61 = lean_array_uset(x_58, x_6, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
x_66 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_67 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_64, x_4);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_65, x_69);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_inc(x_3);
x_75 = lean_array_uset(x_74, x_6, x_3);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = (uint8_t)((x_66 << 24) >> 61);
x_78 = lean_expr_update_forall(x_3, x_77, x_68, x_72);
lean_inc(x_78);
x_79 = lean_array_uset(x_76, x_6, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_70, 1, x_80);
lean_ctor_set(x_70, 0, x_78);
return x_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_70, 0);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_70);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_inc(x_3);
x_84 = lean_array_uset(x_83, x_6, x_3);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = (uint8_t)((x_66 << 24) >> 61);
x_87 = lean_expr_update_forall(x_3, x_86, x_68, x_81);
lean_inc(x_87);
x_88 = lean_array_uset(x_85, x_6, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
case 8:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_3, 3);
lean_inc(x_93);
x_94 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_91, x_4);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_92, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_93, x_99);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_inc(x_3);
x_105 = lean_array_uset(x_104, x_6, x_3);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_expr_update_let(x_3, x_95, x_98, x_102);
lean_inc(x_107);
x_108 = lean_array_uset(x_106, x_6, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_100, 1, x_109);
lean_ctor_set(x_100, 0, x_107);
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_100, 0);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_100);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_inc(x_3);
x_113 = lean_array_uset(x_112, x_6, x_3);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_expr_update_let(x_3, x_95, x_98, x_110);
lean_inc(x_115);
x_116 = lean_array_uset(x_114, x_6, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
case 10:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_3, 1);
lean_inc(x_119);
x_120 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_119, x_4);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_inc(x_3);
x_125 = lean_array_uset(x_124, x_6, x_3);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_expr_update_mdata(x_3, x_122);
lean_inc(x_127);
x_128 = lean_array_uset(x_126, x_6, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_120, 1, x_129);
lean_ctor_set(x_120, 0, x_127);
return x_120;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_inc(x_3);
x_133 = lean_array_uset(x_132, x_6, x_3);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_expr_update_mdata(x_3, x_130);
lean_inc(x_135);
x_136 = lean_array_uset(x_134, x_6, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
case 11:
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_3, 2);
lean_inc(x_139);
x_140 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_2, x_139, x_4);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_inc(x_3);
x_145 = lean_array_uset(x_144, x_6, x_3);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_expr_update_proj(x_3, x_142);
lean_inc(x_147);
x_148 = lean_array_uset(x_146, x_6, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_140, 1, x_149);
lean_ctor_set(x_140, 0, x_147);
return x_140;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_150 = lean_ctor_get(x_140, 0);
x_151 = lean_ctor_get(x_140, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_140);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_inc(x_3);
x_153 = lean_array_uset(x_152, x_6, x_3);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_expr_update_proj(x_3, x_150);
lean_inc(x_155);
x_156 = lean_array_uset(x_154, x_6, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
case 12:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_3);
x_159 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_160 = l_unreachable_x21___rarg(x_159);
x_161 = lean_apply_1(x_160, x_4);
return x_161;
}
default: 
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_3);
lean_ctor_set(x_162, 1, x_4);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_163 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_164 = lean_box(0);
x_165 = l_Lean_mkConst(x_163, x_164);
x_166 = lean_array_uset(x_7, x_6, x_3);
x_167 = lean_ctor_get(x_4, 1);
lean_inc(x_167);
lean_dec(x_4);
lean_inc(x_165);
x_168 = lean_array_uset(x_167, x_6, x_165);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_7);
lean_dec(x_3);
x_171 = lean_ctor_get(x_4, 1);
lean_inc(x_171);
x_172 = lean_array_uget(x_171, x_6);
lean_dec(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_4);
return x_173;
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_preprocessParserBody___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_mkAppStx___closed__3;
x_11 = lean_name_mk_string(x_1, x_10);
x_12 = l_Lean_Expr_isConstOf(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* _init_l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_st_ref_get(x_4, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = l_Std_HashMap_inhabited___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = 1;
x_21 = 0;
x_22 = l_Lean_MetavarContext_MkBinding_mkBinding(x_20, x_17, x_1, x_2, x_21, x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_st_ref_take(x_6, x_15);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_28, 2);
lean_dec(x_31);
lean_ctor_set(x_28, 2, x_26);
x_32 = lean_st_ref_set(x_6, x_28, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_34, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_25);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_26);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_st_ref_set(x_6, x_43, x_29);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
lean_dec(x_24);
x_47 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_46, x_3, x_4, x_5, x_6, x_45);
lean_dec(x_3);
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
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_25);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_52, x_3, x_4, x_5, x_6, x_15);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_st_ref_take(x_6, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_57, 2);
lean_dec(x_60);
lean_ctor_set(x_57, 2, x_55);
x_61 = lean_st_ref_set(x_6, x_57, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_64 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_63, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_3);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
x_67 = lean_ctor_get(x_57, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_58);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_72 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_71, x_3, x_4, x_5, x_6, x_70);
lean_dec(x_3);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_3);
lean_dec(x_1);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_7);
return x_73;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_array_fget(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_20);
x_6 = x_22;
x_7 = x_31;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_20, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_22;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkThunk___closed__1;
x_26 = 0;
x_27 = l_Lean_mkForall(x_25, x_26, x_23, x_7);
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_27;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_5);
x_19 = lean_array_fget(x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_30 = l_Lean_Expr_isConstOf(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_6, x_19);
x_5 = x_21;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_6, x_34);
x_5 = x_21;
x_6 = x_36;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___main___spec__16(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("call of unknown parser at '");
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to generate ");
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" for non-definition '");
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" for non-parser combinator '");
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_23);
x_25 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
lean_inc(x_9);
x_29 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_26, x_28);
x_30 = lean_st_ref_get(x_6, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_35, x_33, x_22);
lean_dec(x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_inc(x_34);
x_37 = l_Lean_Name_append___main(x_22, x_34);
lean_inc(x_22);
x_38 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_22, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_ConstantInfo_type(x_39);
x_42 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_43 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_41, x_42, x_3, x_4, x_5, x_6, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_134; uint8_t x_135; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_134 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_135 = l_Lean_Expr_isConstOf(x_44, x_134);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_137 = l_Lean_Expr_isConstOf(x_44, x_136);
lean_dec(x_44);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_138 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_1);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_141, 0, x_34);
x_142 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_151, x_3, x_4, x_5, x_6, x_140);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_34);
lean_dec(x_9);
x_153 = lean_ctor_get(x_138, 1);
lean_inc(x_153);
lean_dec(x_138);
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
lean_dec(x_139);
x_2 = x_154;
x_7 = x_153;
goto _start;
}
}
else
{
uint8_t x_156; 
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_138);
if (x_156 == 0)
{
return x_138;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_138, 0);
x_158 = lean_ctor_get(x_138, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_138);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; 
x_160 = lean_box(0);
x_46 = x_160;
goto block_133;
}
}
else
{
lean_object* x_161; 
lean_dec(x_44);
x_161 = lean_box(0);
x_46 = x_161;
goto block_133;
}
block_133:
{
lean_object* x_47; 
lean_dec(x_46);
x_47 = l_Lean_ConstantInfo_value_x3f(x_39);
lean_dec(x_39);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_1);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_34);
x_49 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_58, x_3, x_4, x_5, x_6, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_34);
lean_dec(x_9);
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
lean_dec(x_47);
x_61 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_62 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_61, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_82 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_83 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed), 9, 2);
lean_closure_set(x_83, 0, x_1);
lean_closure_set(x_83, 1, x_82);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_41, x_83, x_3, x_4, x_5, x_6, x_64);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(0);
lean_inc(x_37);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_37);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_85);
x_89 = lean_box(0);
x_90 = 0;
x_91 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_63);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_st_ref_get(x_6, x_86);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Environment_addAndCompile(x_96, x_87, x_92);
lean_dec(x_92);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_1);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_KernelException_toMessageData(x_98, x_87);
x_100 = lean_ctor_get(x_5, 3);
lean_inc(x_100);
x_101 = l_Lean_MessageData_toString(x_99, x_95);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_105, x_3, x_4, x_5, x_6, x_103);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
return x_106;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_101);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_101, 0);
x_113 = lean_io_error_to_string(x_112);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_100);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_101, 0, x_116);
return x_101;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_101, 0);
x_118 = lean_ctor_get(x_101, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_101);
x_119 = lean_io_error_to_string(x_117);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_100);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_97, 0);
lean_inc(x_124);
lean_dec(x_97);
x_65 = x_124;
x_66 = x_95;
goto block_81;
}
}
else
{
uint8_t x_125; 
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_84);
if (x_125 == 0)
{
return x_84;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_84, 0);
x_127 = lean_ctor_get(x_84, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_84);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
block_81:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_37);
x_67 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_35, x_65, x_22, x_37);
x_68 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_67, x_3, x_4, x_5, x_6, x_66);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = l_Lean_mkConst(x_37, x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_71);
x_72 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_71, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed), 11, 4);
lean_closure_set(x_75, 0, x_1);
lean_closure_set(x_75, 1, x_42);
lean_closure_set(x_75, 2, x_29);
lean_closure_set(x_75, 3, x_71);
x_76 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_73, x_75, x_3, x_4, x_5, x_6, x_74);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_71);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_62);
if (x_129 == 0)
{
return x_62;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_62, 0);
x_131 = lean_ctor_get(x_62, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_62);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_43);
if (x_162 == 0)
{
return x_43;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_43, 0);
x_164 = lean_ctor_get(x_43, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_43);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_38);
if (x_166 == 0)
{
return x_38;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_38, 0);
x_168 = lean_ctor_get(x_38, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_38);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
x_170 = lean_ctor_get(x_36, 0);
lean_inc(x_170);
lean_dec(x_36);
x_171 = lean_box(0);
x_172 = l_Lean_mkConst(x_170, x_171);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_172);
x_173 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_172, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed), 10, 3);
lean_closure_set(x_176, 0, x_1);
lean_closure_set(x_176, 1, x_29);
lean_closure_set(x_176, 2, x_172);
x_177 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_174, x_176, x_3, x_4, x_5, x_6, x_175);
return x_177;
}
else
{
uint8_t x_178; 
lean_dec(x_172);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_173);
if (x_178 == 0)
{
return x_173;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_173);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
else
{
lean_object* x_182; 
lean_dec(x_11);
lean_dec(x_1);
x_182 = lean_box(0);
x_12 = x_182;
goto block_21;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_13 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
case 1:
{
uint8_t x_183; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_8);
if (x_183 == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_8, 0);
lean_dec(x_184);
return x_8;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_8, 1);
lean_inc(x_185);
lean_dec(x_8);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_9);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
case 2:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_8, 1);
lean_inc(x_187);
lean_dec(x_8);
x_188 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_188) == 4)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_199 = lean_ctor_get(x_188, 0);
lean_inc(x_199);
lean_dec(x_188);
x_200 = lean_unsigned_to_nat(0u);
x_201 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_200);
x_202 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_201);
x_203 = lean_mk_array(x_201, x_202);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_sub(x_201, x_204);
lean_dec(x_201);
lean_inc(x_9);
x_206 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_203, x_205);
x_207 = lean_st_ref_get(x_6, x_187);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_ctor_get(x_1, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_1, 2);
lean_inc(x_212);
x_213 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_212, x_210, x_199);
lean_dec(x_210);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_inc(x_211);
x_214 = l_Lean_Name_append___main(x_199, x_211);
lean_inc(x_199);
x_215 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_199, x_3, x_4, x_5, x_6, x_209);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_ConstantInfo_type(x_216);
x_219 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_220 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_218, x_219, x_3, x_4, x_5, x_6, x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_311; uint8_t x_312; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_311 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_312 = l_Lean_Expr_isConstOf(x_221, x_311);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_314 = l_Lean_Expr_isConstOf(x_221, x_313);
lean_dec(x_221);
if (x_314 == 0)
{
lean_object* x_315; 
lean_dec(x_218);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_199);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_315 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_222);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_1);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_318, 0, x_211);
x_319 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_320 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_322 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_324 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_324, 0, x_323);
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_328 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_328, x_3, x_4, x_5, x_6, x_317);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_211);
lean_dec(x_9);
x_330 = lean_ctor_get(x_315, 1);
lean_inc(x_330);
lean_dec(x_315);
x_331 = lean_ctor_get(x_316, 0);
lean_inc(x_331);
lean_dec(x_316);
x_2 = x_331;
x_7 = x_330;
goto _start;
}
}
else
{
uint8_t x_333; 
lean_dec(x_211);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_333 = !lean_is_exclusive(x_315);
if (x_333 == 0)
{
return x_315;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_315, 0);
x_335 = lean_ctor_get(x_315, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_315);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
lean_object* x_337; 
x_337 = lean_box(0);
x_223 = x_337;
goto block_310;
}
}
else
{
lean_object* x_338; 
lean_dec(x_221);
x_338 = lean_box(0);
x_223 = x_338;
goto block_310;
}
block_310:
{
lean_object* x_224; 
lean_dec(x_223);
x_224 = l_Lean_ConstantInfo_value_x3f(x_216);
lean_dec(x_216);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_1);
x_225 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_225, 0, x_211);
x_226 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_227 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_229 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_231 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_233 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_235, x_3, x_4, x_5, x_6, x_222);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_211);
lean_dec(x_9);
x_237 = lean_ctor_get(x_224, 0);
lean_inc(x_237);
lean_dec(x_224);
x_238 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_237);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_239 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_238, x_3, x_4, x_5, x_6, x_222);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_259 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_260 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed), 9, 2);
lean_closure_set(x_260, 0, x_1);
lean_closure_set(x_260, 1, x_259);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_261 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_218, x_260, x_3, x_4, x_5, x_6, x_241);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_box(0);
lean_inc(x_214);
x_265 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_265, 0, x_214);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set(x_265, 2, x_262);
x_266 = lean_box(0);
x_267 = 0;
x_268 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_240);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*3, x_267);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_st_ref_get(x_6, x_263);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_Lean_Environment_addAndCompile(x_273, x_264, x_269);
lean_dec(x_269);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_1);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Lean_KernelException_toMessageData(x_275, x_264);
x_277 = lean_ctor_get(x_5, 3);
lean_inc(x_277);
x_278 = l_Lean_MessageData_toString(x_276, x_272);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_277);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_281, 0, x_279);
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_281);
x_283 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_282, x_3, x_4, x_5, x_6, x_280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
return x_283;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_283, 0);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_283);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
else
{
uint8_t x_288; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_288 = !lean_is_exclusive(x_278);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_278, 0);
x_290 = lean_io_error_to_string(x_289);
x_291 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_277);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_278, 0, x_293);
return x_278;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_278, 0);
x_295 = lean_ctor_get(x_278, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_278);
x_296 = lean_io_error_to_string(x_294);
x_297 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_277);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_295);
return x_300;
}
}
}
else
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_274, 0);
lean_inc(x_301);
lean_dec(x_274);
x_242 = x_301;
x_243 = x_272;
goto block_258;
}
}
else
{
uint8_t x_302; 
lean_dec(x_240);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_261);
if (x_302 == 0)
{
return x_261;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_261, 0);
x_304 = lean_ctor_get(x_261, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_261);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
block_258:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_inc(x_214);
x_244 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_212, x_242, x_199, x_214);
x_245 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_244, x_3, x_4, x_5, x_6, x_243);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_box(0);
x_248 = l_Lean_mkConst(x_214, x_247);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_248);
x_249 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_248, x_3, x_4, x_5, x_6, x_246);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed), 11, 4);
lean_closure_set(x_252, 0, x_1);
lean_closure_set(x_252, 1, x_219);
lean_closure_set(x_252, 2, x_206);
lean_closure_set(x_252, 3, x_248);
x_253 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_250, x_252, x_3, x_4, x_5, x_6, x_251);
return x_253;
}
else
{
uint8_t x_254; 
lean_dec(x_248);
lean_dec(x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_249);
if (x_254 == 0)
{
return x_249;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_249, 0);
x_256 = lean_ctor_get(x_249, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_249);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_239);
if (x_306 == 0)
{
return x_239;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_239, 0);
x_308 = lean_ctor_get(x_239, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_239);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_218);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_220);
if (x_339 == 0)
{
return x_220;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_220, 0);
x_341 = lean_ctor_get(x_220, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_220);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_343 = !lean_is_exclusive(x_215);
if (x_343 == 0)
{
return x_215;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_215, 0);
x_345 = lean_ctor_get(x_215, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_215);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_199);
lean_dec(x_9);
x_347 = lean_ctor_get(x_213, 0);
lean_inc(x_347);
lean_dec(x_213);
x_348 = lean_box(0);
x_349 = l_Lean_mkConst(x_347, x_348);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_349);
x_350 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_349, x_3, x_4, x_5, x_6, x_209);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed), 10, 3);
lean_closure_set(x_353, 0, x_1);
lean_closure_set(x_353, 1, x_206);
lean_closure_set(x_353, 2, x_349);
x_354 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_351, x_353, x_3, x_4, x_5, x_6, x_352);
return x_354;
}
else
{
uint8_t x_355; 
lean_dec(x_349);
lean_dec(x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_355 = !lean_is_exclusive(x_350);
if (x_355 == 0)
{
return x_350;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_350, 0);
x_357 = lean_ctor_get(x_350, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_350);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
}
else
{
lean_object* x_359; 
lean_dec(x_188);
lean_dec(x_1);
x_359 = lean_box(0);
x_189 = x_359;
goto block_198;
}
block_198:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_189);
x_190 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_194 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_196 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_196, x_3, x_4, x_5, x_6, x_187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_197;
}
}
case 3:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_8, 1);
lean_inc(x_360);
lean_dec(x_8);
x_361 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_361) == 4)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_372 = lean_ctor_get(x_361, 0);
lean_inc(x_372);
lean_dec(x_361);
x_373 = lean_unsigned_to_nat(0u);
x_374 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_373);
x_375 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_374);
x_376 = lean_mk_array(x_374, x_375);
x_377 = lean_unsigned_to_nat(1u);
x_378 = lean_nat_sub(x_374, x_377);
lean_dec(x_374);
lean_inc(x_9);
x_379 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_376, x_378);
x_380 = lean_st_ref_get(x_6, x_360);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_1, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_1, 2);
lean_inc(x_385);
x_386 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_385, x_383, x_372);
lean_dec(x_383);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_inc(x_384);
x_387 = l_Lean_Name_append___main(x_372, x_384);
lean_inc(x_372);
x_388 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_372, x_3, x_4, x_5, x_6, x_382);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_ConstantInfo_type(x_389);
x_392 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_391);
x_393 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_391, x_392, x_3, x_4, x_5, x_6, x_390);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_484; uint8_t x_485; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_484 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_485 = l_Lean_Expr_isConstOf(x_394, x_484);
if (x_485 == 0)
{
lean_object* x_486; uint8_t x_487; 
x_486 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_487 = l_Lean_Expr_isConstOf(x_394, x_486);
lean_dec(x_394);
if (x_487 == 0)
{
lean_object* x_488; 
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_372);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_488 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_395);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_1);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_491, 0, x_384);
x_492 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_493 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
x_494 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_495 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
x_496 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_497 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_498 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_498, 0, x_497);
x_499 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_499, 0, x_495);
lean_ctor_set(x_499, 1, x_498);
x_500 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_501 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
x_502 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_501, x_3, x_4, x_5, x_6, x_490);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; 
lean_dec(x_384);
lean_dec(x_9);
x_503 = lean_ctor_get(x_488, 1);
lean_inc(x_503);
lean_dec(x_488);
x_504 = lean_ctor_get(x_489, 0);
lean_inc(x_504);
lean_dec(x_489);
x_2 = x_504;
x_7 = x_503;
goto _start;
}
}
else
{
uint8_t x_506; 
lean_dec(x_384);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_488);
if (x_506 == 0)
{
return x_488;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_488, 0);
x_508 = lean_ctor_get(x_488, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_488);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
else
{
lean_object* x_510; 
x_510 = lean_box(0);
x_396 = x_510;
goto block_483;
}
}
else
{
lean_object* x_511; 
lean_dec(x_394);
x_511 = lean_box(0);
x_396 = x_511;
goto block_483;
}
block_483:
{
lean_object* x_397; 
lean_dec(x_396);
x_397 = l_Lean_ConstantInfo_value_x3f(x_389);
lean_dec(x_389);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_391);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_1);
x_398 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_398, 0, x_384);
x_399 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_400 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_401 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_402 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_404 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_404, 0, x_403);
x_405 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_408 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
x_409 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_408, x_3, x_4, x_5, x_6, x_395);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_384);
lean_dec(x_9);
x_410 = lean_ctor_get(x_397, 0);
lean_inc(x_410);
lean_dec(x_397);
x_411 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_410);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_412 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_411, x_3, x_4, x_5, x_6, x_395);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_432 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_433 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed), 9, 2);
lean_closure_set(x_433, 0, x_1);
lean_closure_set(x_433, 1, x_432);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_434 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_391, x_433, x_3, x_4, x_5, x_6, x_414);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = lean_box(0);
lean_inc(x_387);
x_438 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_438, 0, x_387);
lean_ctor_set(x_438, 1, x_437);
lean_ctor_set(x_438, 2, x_435);
x_439 = lean_box(0);
x_440 = 0;
x_441 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_413);
lean_ctor_set(x_441, 2, x_439);
lean_ctor_set_uint8(x_441, sizeof(void*)*3, x_440);
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_441);
x_443 = lean_st_ref_get(x_6, x_436);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
lean_dec(x_444);
x_447 = l_Lean_Environment_addAndCompile(x_446, x_437, x_442);
lean_dec(x_442);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_1);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec(x_447);
x_449 = l_Lean_KernelException_toMessageData(x_448, x_437);
x_450 = lean_ctor_get(x_5, 3);
lean_inc(x_450);
x_451 = l_Lean_MessageData_toString(x_449, x_445);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
lean_dec(x_450);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_454, 0, x_452);
x_455 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_455, 0, x_454);
x_456 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_455, x_3, x_4, x_5, x_6, x_453);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_457 = !lean_is_exclusive(x_456);
if (x_457 == 0)
{
return x_456;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_456, 0);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_456);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
else
{
uint8_t x_461; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_461 = !lean_is_exclusive(x_451);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_462 = lean_ctor_get(x_451, 0);
x_463 = lean_io_error_to_string(x_462);
x_464 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_465 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_465, 0, x_464);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_450);
lean_ctor_set(x_466, 1, x_465);
lean_ctor_set(x_451, 0, x_466);
return x_451;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_467 = lean_ctor_get(x_451, 0);
x_468 = lean_ctor_get(x_451, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_451);
x_469 = lean_io_error_to_string(x_467);
x_470 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_470, 0, x_469);
x_471 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_471, 0, x_470);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_450);
lean_ctor_set(x_472, 1, x_471);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_468);
return x_473;
}
}
}
else
{
lean_object* x_474; 
x_474 = lean_ctor_get(x_447, 0);
lean_inc(x_474);
lean_dec(x_447);
x_415 = x_474;
x_416 = x_445;
goto block_431;
}
}
else
{
uint8_t x_475; 
lean_dec(x_413);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_475 = !lean_is_exclusive(x_434);
if (x_475 == 0)
{
return x_434;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_434, 0);
x_477 = lean_ctor_get(x_434, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_434);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
block_431:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_inc(x_387);
x_417 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_385, x_415, x_372, x_387);
x_418 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_417, x_3, x_4, x_5, x_6, x_416);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
x_420 = lean_box(0);
x_421 = l_Lean_mkConst(x_387, x_420);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_421);
x_422 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_421, x_3, x_4, x_5, x_6, x_419);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed), 11, 4);
lean_closure_set(x_425, 0, x_1);
lean_closure_set(x_425, 1, x_392);
lean_closure_set(x_425, 2, x_379);
lean_closure_set(x_425, 3, x_421);
x_426 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_423, x_425, x_3, x_4, x_5, x_6, x_424);
return x_426;
}
else
{
uint8_t x_427; 
lean_dec(x_421);
lean_dec(x_379);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_427 = !lean_is_exclusive(x_422);
if (x_427 == 0)
{
return x_422;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_422, 0);
x_429 = lean_ctor_get(x_422, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_422);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
}
else
{
uint8_t x_479; 
lean_dec(x_391);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_479 = !lean_is_exclusive(x_412);
if (x_479 == 0)
{
return x_412;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_412, 0);
x_481 = lean_ctor_get(x_412, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_412);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
}
}
else
{
uint8_t x_512; 
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_512 = !lean_is_exclusive(x_393);
if (x_512 == 0)
{
return x_393;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_393, 0);
x_514 = lean_ctor_get(x_393, 1);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_393);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_513);
lean_ctor_set(x_515, 1, x_514);
return x_515;
}
}
}
else
{
uint8_t x_516; 
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_516 = !lean_is_exclusive(x_388);
if (x_516 == 0)
{
return x_388;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_388, 0);
x_518 = lean_ctor_get(x_388, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_388);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_372);
lean_dec(x_9);
x_520 = lean_ctor_get(x_386, 0);
lean_inc(x_520);
lean_dec(x_386);
x_521 = lean_box(0);
x_522 = l_Lean_mkConst(x_520, x_521);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_522);
x_523 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_522, x_3, x_4, x_5, x_6, x_382);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed), 10, 3);
lean_closure_set(x_526, 0, x_1);
lean_closure_set(x_526, 1, x_379);
lean_closure_set(x_526, 2, x_522);
x_527 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_524, x_526, x_3, x_4, x_5, x_6, x_525);
return x_527;
}
else
{
uint8_t x_528; 
lean_dec(x_522);
lean_dec(x_379);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_528 = !lean_is_exclusive(x_523);
if (x_528 == 0)
{
return x_523;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_523, 0);
x_530 = lean_ctor_get(x_523, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_523);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
}
else
{
lean_object* x_532; 
lean_dec(x_361);
lean_dec(x_1);
x_532 = lean_box(0);
x_362 = x_532;
goto block_371;
}
block_371:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_362);
x_363 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_364 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_364, 0, x_363);
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_364);
x_366 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_367 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_369 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_369, x_3, x_4, x_5, x_6, x_360);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_370;
}
}
case 4:
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_8, 1);
lean_inc(x_533);
lean_dec(x_8);
x_534 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_534) == 4)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_545 = lean_ctor_get(x_534, 0);
lean_inc(x_545);
lean_dec(x_534);
x_546 = lean_unsigned_to_nat(0u);
x_547 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_546);
x_548 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_547);
x_549 = lean_mk_array(x_547, x_548);
x_550 = lean_unsigned_to_nat(1u);
x_551 = lean_nat_sub(x_547, x_550);
lean_dec(x_547);
lean_inc(x_9);
x_552 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_549, x_551);
x_553 = lean_st_ref_get(x_6, x_533);
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = lean_ctor_get(x_554, 0);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_ctor_get(x_1, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_1, 2);
lean_inc(x_558);
x_559 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_558, x_556, x_545);
lean_dec(x_556);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
lean_inc(x_557);
x_560 = l_Lean_Name_append___main(x_545, x_557);
lean_inc(x_545);
x_561 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_545, x_3, x_4, x_5, x_6, x_555);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = l_Lean_ConstantInfo_type(x_562);
x_565 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_564);
x_566 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_564, x_565, x_3, x_4, x_5, x_6, x_563);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_657; uint8_t x_658; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_657 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_658 = l_Lean_Expr_isConstOf(x_567, x_657);
if (x_658 == 0)
{
lean_object* x_659; uint8_t x_660; 
x_659 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_660 = l_Lean_Expr_isConstOf(x_567, x_659);
lean_dec(x_567);
if (x_660 == 0)
{
lean_object* x_661; 
lean_dec(x_564);
lean_dec(x_562);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_552);
lean_dec(x_545);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_661 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_568);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_1);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
x_664 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_664, 0, x_557);
x_665 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_666 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_664);
x_667 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_668 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
x_669 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_670 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_670, 0, x_669);
x_671 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_671, 0, x_670);
x_672 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_672, 0, x_668);
lean_ctor_set(x_672, 1, x_671);
x_673 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_674 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
x_675 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_674, x_3, x_4, x_5, x_6, x_663);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_675;
}
else
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_557);
lean_dec(x_9);
x_676 = lean_ctor_get(x_661, 1);
lean_inc(x_676);
lean_dec(x_661);
x_677 = lean_ctor_get(x_662, 0);
lean_inc(x_677);
lean_dec(x_662);
x_2 = x_677;
x_7 = x_676;
goto _start;
}
}
else
{
uint8_t x_679; 
lean_dec(x_557);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_679 = !lean_is_exclusive(x_661);
if (x_679 == 0)
{
return x_661;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_661, 0);
x_681 = lean_ctor_get(x_661, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_661);
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_680);
lean_ctor_set(x_682, 1, x_681);
return x_682;
}
}
}
else
{
lean_object* x_683; 
x_683 = lean_box(0);
x_569 = x_683;
goto block_656;
}
}
else
{
lean_object* x_684; 
lean_dec(x_567);
x_684 = lean_box(0);
x_569 = x_684;
goto block_656;
}
block_656:
{
lean_object* x_570; 
lean_dec(x_569);
x_570 = l_Lean_ConstantInfo_value_x3f(x_562);
lean_dec(x_562);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_564);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_552);
lean_dec(x_545);
lean_dec(x_1);
x_571 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_571, 0, x_557);
x_572 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_573 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_573, 1, x_571);
x_574 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_575 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_577 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_577, 0, x_576);
x_578 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_578, 0, x_577);
x_579 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_579, 0, x_575);
lean_ctor_set(x_579, 1, x_578);
x_580 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_581 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_581, x_3, x_4, x_5, x_6, x_568);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_557);
lean_dec(x_9);
x_583 = lean_ctor_get(x_570, 0);
lean_inc(x_583);
lean_dec(x_570);
x_584 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_583);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_585 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_584, x_3, x_4, x_5, x_6, x_568);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_605 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_606 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed), 9, 2);
lean_closure_set(x_606, 0, x_1);
lean_closure_set(x_606, 1, x_605);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_607 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_564, x_606, x_3, x_4, x_5, x_6, x_587);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = lean_box(0);
lean_inc(x_560);
x_611 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_611, 0, x_560);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_611, 2, x_608);
x_612 = lean_box(0);
x_613 = 0;
x_614 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_614, 0, x_611);
lean_ctor_set(x_614, 1, x_586);
lean_ctor_set(x_614, 2, x_612);
lean_ctor_set_uint8(x_614, sizeof(void*)*3, x_613);
x_615 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_615, 0, x_614);
x_616 = lean_st_ref_get(x_6, x_609);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
lean_dec(x_617);
x_620 = l_Lean_Environment_addAndCompile(x_619, x_610, x_615);
lean_dec(x_615);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_552);
lean_dec(x_545);
lean_dec(x_1);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
lean_dec(x_620);
x_622 = l_Lean_KernelException_toMessageData(x_621, x_610);
x_623 = lean_ctor_get(x_5, 3);
lean_inc(x_623);
x_624 = l_Lean_MessageData_toString(x_622, x_618);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
lean_dec(x_623);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_627, 0, x_625);
x_628 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_628, 0, x_627);
x_629 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_628, x_3, x_4, x_5, x_6, x_626);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_630 = !lean_is_exclusive(x_629);
if (x_630 == 0)
{
return x_629;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_629, 0);
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_629);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
else
{
uint8_t x_634; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_634 = !lean_is_exclusive(x_624);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_635 = lean_ctor_get(x_624, 0);
x_636 = lean_io_error_to_string(x_635);
x_637 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_637, 0, x_636);
x_638 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_638, 0, x_637);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_623);
lean_ctor_set(x_639, 1, x_638);
lean_ctor_set(x_624, 0, x_639);
return x_624;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_640 = lean_ctor_get(x_624, 0);
x_641 = lean_ctor_get(x_624, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_624);
x_642 = lean_io_error_to_string(x_640);
x_643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_623);
lean_ctor_set(x_645, 1, x_644);
x_646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_641);
return x_646;
}
}
}
else
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_620, 0);
lean_inc(x_647);
lean_dec(x_620);
x_588 = x_647;
x_589 = x_618;
goto block_604;
}
}
else
{
uint8_t x_648; 
lean_dec(x_586);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_552);
lean_dec(x_545);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_648 = !lean_is_exclusive(x_607);
if (x_648 == 0)
{
return x_607;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_607, 0);
x_650 = lean_ctor_get(x_607, 1);
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_607);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
return x_651;
}
}
block_604:
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_inc(x_560);
x_590 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_558, x_588, x_545, x_560);
x_591 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_590, x_3, x_4, x_5, x_6, x_589);
x_592 = lean_ctor_get(x_591, 1);
lean_inc(x_592);
lean_dec(x_591);
x_593 = lean_box(0);
x_594 = l_Lean_mkConst(x_560, x_593);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_595 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_594, x_3, x_4, x_5, x_6, x_592);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed), 11, 4);
lean_closure_set(x_598, 0, x_1);
lean_closure_set(x_598, 1, x_565);
lean_closure_set(x_598, 2, x_552);
lean_closure_set(x_598, 3, x_594);
x_599 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_596, x_598, x_3, x_4, x_5, x_6, x_597);
return x_599;
}
else
{
uint8_t x_600; 
lean_dec(x_594);
lean_dec(x_552);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_600 = !lean_is_exclusive(x_595);
if (x_600 == 0)
{
return x_595;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_595, 0);
x_602 = lean_ctor_get(x_595, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_595);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_564);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_552);
lean_dec(x_545);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_652 = !lean_is_exclusive(x_585);
if (x_652 == 0)
{
return x_585;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_585, 0);
x_654 = lean_ctor_get(x_585, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_585);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
return x_655;
}
}
}
}
}
else
{
uint8_t x_685; 
lean_dec(x_564);
lean_dec(x_562);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_545);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_685 = !lean_is_exclusive(x_566);
if (x_685 == 0)
{
return x_566;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_566, 0);
x_687 = lean_ctor_get(x_566, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_566);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
else
{
uint8_t x_689; 
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_545);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_689 = !lean_is_exclusive(x_561);
if (x_689 == 0)
{
return x_561;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_690 = lean_ctor_get(x_561, 0);
x_691 = lean_ctor_get(x_561, 1);
lean_inc(x_691);
lean_inc(x_690);
lean_dec(x_561);
x_692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_692, 0, x_690);
lean_ctor_set(x_692, 1, x_691);
return x_692;
}
}
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_545);
lean_dec(x_9);
x_693 = lean_ctor_get(x_559, 0);
lean_inc(x_693);
lean_dec(x_559);
x_694 = lean_box(0);
x_695 = l_Lean_mkConst(x_693, x_694);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_695);
x_696 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_695, x_3, x_4, x_5, x_6, x_555);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed), 10, 3);
lean_closure_set(x_699, 0, x_1);
lean_closure_set(x_699, 1, x_552);
lean_closure_set(x_699, 2, x_695);
x_700 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_697, x_699, x_3, x_4, x_5, x_6, x_698);
return x_700;
}
else
{
uint8_t x_701; 
lean_dec(x_695);
lean_dec(x_552);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_701 = !lean_is_exclusive(x_696);
if (x_701 == 0)
{
return x_696;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_696, 0);
x_703 = lean_ctor_get(x_696, 1);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_696);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
return x_704;
}
}
}
}
else
{
lean_object* x_705; 
lean_dec(x_534);
lean_dec(x_1);
x_705 = lean_box(0);
x_535 = x_705;
goto block_544;
}
block_544:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_535);
x_536 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_537 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_537, 0, x_536);
x_538 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_538, 0, x_537);
x_539 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_540 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_538);
x_541 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_542 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_541);
x_543 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_542, x_3, x_4, x_5, x_6, x_533);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_543;
}
}
case 5:
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_8, 1);
lean_inc(x_706);
lean_dec(x_8);
x_707 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_707) == 4)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_718 = lean_ctor_get(x_707, 0);
lean_inc(x_718);
lean_dec(x_707);
x_719 = lean_unsigned_to_nat(0u);
x_720 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_719);
x_721 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_720);
x_722 = lean_mk_array(x_720, x_721);
x_723 = lean_unsigned_to_nat(1u);
x_724 = lean_nat_sub(x_720, x_723);
lean_dec(x_720);
lean_inc(x_9);
x_725 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_722, x_724);
x_726 = lean_st_ref_get(x_6, x_706);
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
lean_dec(x_726);
x_729 = lean_ctor_get(x_727, 0);
lean_inc(x_729);
lean_dec(x_727);
x_730 = lean_ctor_get(x_1, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_1, 2);
lean_inc(x_731);
x_732 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_731, x_729, x_718);
lean_dec(x_729);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; 
lean_inc(x_730);
x_733 = l_Lean_Name_append___main(x_718, x_730);
lean_inc(x_718);
x_734 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_718, x_3, x_4, x_5, x_6, x_728);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = l_Lean_ConstantInfo_type(x_735);
x_738 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_737);
x_739 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_737, x_738, x_3, x_4, x_5, x_6, x_736);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_830; uint8_t x_831; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_830 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_831 = l_Lean_Expr_isConstOf(x_740, x_830);
if (x_831 == 0)
{
lean_object* x_832; uint8_t x_833; 
x_832 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_833 = l_Lean_Expr_isConstOf(x_740, x_832);
lean_dec(x_740);
if (x_833 == 0)
{
lean_object* x_834; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_725);
lean_dec(x_718);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_834 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_741);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; 
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_1);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
lean_dec(x_834);
x_837 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_837, 0, x_730);
x_838 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_839 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_837);
x_840 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_841 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
x_842 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_843 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_843, 0, x_842);
x_844 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_844, 0, x_843);
x_845 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_845, 0, x_841);
lean_ctor_set(x_845, 1, x_844);
x_846 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_847 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
x_848 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_847, x_3, x_4, x_5, x_6, x_836);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_848;
}
else
{
lean_object* x_849; lean_object* x_850; 
lean_dec(x_730);
lean_dec(x_9);
x_849 = lean_ctor_get(x_834, 1);
lean_inc(x_849);
lean_dec(x_834);
x_850 = lean_ctor_get(x_835, 0);
lean_inc(x_850);
lean_dec(x_835);
x_2 = x_850;
x_7 = x_849;
goto _start;
}
}
else
{
uint8_t x_852; 
lean_dec(x_730);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_852 = !lean_is_exclusive(x_834);
if (x_852 == 0)
{
return x_834;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_834, 0);
x_854 = lean_ctor_get(x_834, 1);
lean_inc(x_854);
lean_inc(x_853);
lean_dec(x_834);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_853);
lean_ctor_set(x_855, 1, x_854);
return x_855;
}
}
}
else
{
lean_object* x_856; 
x_856 = lean_box(0);
x_742 = x_856;
goto block_829;
}
}
else
{
lean_object* x_857; 
lean_dec(x_740);
x_857 = lean_box(0);
x_742 = x_857;
goto block_829;
}
block_829:
{
lean_object* x_743; 
lean_dec(x_742);
x_743 = l_Lean_ConstantInfo_value_x3f(x_735);
lean_dec(x_735);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_725);
lean_dec(x_718);
lean_dec(x_1);
x_744 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_744, 0, x_730);
x_745 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_746 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_744);
x_747 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_748 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
x_749 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_750 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_750, 0, x_749);
x_751 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_751, 0, x_750);
x_752 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_752, 0, x_748);
lean_ctor_set(x_752, 1, x_751);
x_753 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_754 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
x_755 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_754, x_3, x_4, x_5, x_6, x_741);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_755;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_730);
lean_dec(x_9);
x_756 = lean_ctor_get(x_743, 0);
lean_inc(x_756);
lean_dec(x_743);
x_757 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_756);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_758 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_757, x_3, x_4, x_5, x_6, x_741);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_778 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_779 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed), 9, 2);
lean_closure_set(x_779, 0, x_1);
lean_closure_set(x_779, 1, x_778);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_780 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_737, x_779, x_3, x_4, x_5, x_6, x_760);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = lean_box(0);
lean_inc(x_733);
x_784 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_784, 0, x_733);
lean_ctor_set(x_784, 1, x_783);
lean_ctor_set(x_784, 2, x_781);
x_785 = lean_box(0);
x_786 = 0;
x_787 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_787, 0, x_784);
lean_ctor_set(x_787, 1, x_759);
lean_ctor_set(x_787, 2, x_785);
lean_ctor_set_uint8(x_787, sizeof(void*)*3, x_786);
x_788 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_788, 0, x_787);
x_789 = lean_st_ref_get(x_6, x_782);
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = lean_ctor_get(x_790, 0);
lean_inc(x_792);
lean_dec(x_790);
x_793 = l_Lean_Environment_addAndCompile(x_792, x_783, x_788);
lean_dec(x_788);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_725);
lean_dec(x_718);
lean_dec(x_1);
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
lean_dec(x_793);
x_795 = l_Lean_KernelException_toMessageData(x_794, x_783);
x_796 = lean_ctor_get(x_5, 3);
lean_inc(x_796);
x_797 = l_Lean_MessageData_toString(x_795, x_791);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; uint8_t x_803; 
lean_dec(x_796);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec(x_797);
x_800 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_800, 0, x_798);
x_801 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_801, 0, x_800);
x_802 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_801, x_3, x_4, x_5, x_6, x_799);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_803 = !lean_is_exclusive(x_802);
if (x_803 == 0)
{
return x_802;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_802, 0);
x_805 = lean_ctor_get(x_802, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_802);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
else
{
uint8_t x_807; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_807 = !lean_is_exclusive(x_797);
if (x_807 == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_808 = lean_ctor_get(x_797, 0);
x_809 = lean_io_error_to_string(x_808);
x_810 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_810, 0, x_809);
x_811 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_811, 0, x_810);
x_812 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_812, 0, x_796);
lean_ctor_set(x_812, 1, x_811);
lean_ctor_set(x_797, 0, x_812);
return x_797;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_813 = lean_ctor_get(x_797, 0);
x_814 = lean_ctor_get(x_797, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_797);
x_815 = lean_io_error_to_string(x_813);
x_816 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_816, 0, x_815);
x_817 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_817, 0, x_816);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_796);
lean_ctor_set(x_818, 1, x_817);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_814);
return x_819;
}
}
}
else
{
lean_object* x_820; 
x_820 = lean_ctor_get(x_793, 0);
lean_inc(x_820);
lean_dec(x_793);
x_761 = x_820;
x_762 = x_791;
goto block_777;
}
}
else
{
uint8_t x_821; 
lean_dec(x_759);
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_725);
lean_dec(x_718);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_821 = !lean_is_exclusive(x_780);
if (x_821 == 0)
{
return x_780;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_780, 0);
x_823 = lean_ctor_get(x_780, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_780);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
block_777:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_inc(x_733);
x_763 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_731, x_761, x_718, x_733);
x_764 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_763, x_3, x_4, x_5, x_6, x_762);
x_765 = lean_ctor_get(x_764, 1);
lean_inc(x_765);
lean_dec(x_764);
x_766 = lean_box(0);
x_767 = l_Lean_mkConst(x_733, x_766);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_767);
x_768 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_767, x_3, x_4, x_5, x_6, x_765);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed), 11, 4);
lean_closure_set(x_771, 0, x_1);
lean_closure_set(x_771, 1, x_738);
lean_closure_set(x_771, 2, x_725);
lean_closure_set(x_771, 3, x_767);
x_772 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_769, x_771, x_3, x_4, x_5, x_6, x_770);
return x_772;
}
else
{
uint8_t x_773; 
lean_dec(x_767);
lean_dec(x_725);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_773 = !lean_is_exclusive(x_768);
if (x_773 == 0)
{
return x_768;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_768, 0);
x_775 = lean_ctor_get(x_768, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_768);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
}
else
{
uint8_t x_825; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_725);
lean_dec(x_718);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_825 = !lean_is_exclusive(x_758);
if (x_825 == 0)
{
return x_758;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_758, 0);
x_827 = lean_ctor_get(x_758, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_758);
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_826);
lean_ctor_set(x_828, 1, x_827);
return x_828;
}
}
}
}
}
else
{
uint8_t x_858; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_730);
lean_dec(x_725);
lean_dec(x_718);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_858 = !lean_is_exclusive(x_739);
if (x_858 == 0)
{
return x_739;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_859 = lean_ctor_get(x_739, 0);
x_860 = lean_ctor_get(x_739, 1);
lean_inc(x_860);
lean_inc(x_859);
lean_dec(x_739);
x_861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set(x_861, 1, x_860);
return x_861;
}
}
}
else
{
uint8_t x_862; 
lean_dec(x_733);
lean_dec(x_731);
lean_dec(x_730);
lean_dec(x_725);
lean_dec(x_718);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_862 = !lean_is_exclusive(x_734);
if (x_862 == 0)
{
return x_734;
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_734, 0);
x_864 = lean_ctor_get(x_734, 1);
lean_inc(x_864);
lean_inc(x_863);
lean_dec(x_734);
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_863);
lean_ctor_set(x_865, 1, x_864);
return x_865;
}
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_731);
lean_dec(x_730);
lean_dec(x_718);
lean_dec(x_9);
x_866 = lean_ctor_get(x_732, 0);
lean_inc(x_866);
lean_dec(x_732);
x_867 = lean_box(0);
x_868 = l_Lean_mkConst(x_866, x_867);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_868);
x_869 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_868, x_3, x_4, x_5, x_6, x_728);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed), 10, 3);
lean_closure_set(x_872, 0, x_1);
lean_closure_set(x_872, 1, x_725);
lean_closure_set(x_872, 2, x_868);
x_873 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_870, x_872, x_3, x_4, x_5, x_6, x_871);
return x_873;
}
else
{
uint8_t x_874; 
lean_dec(x_868);
lean_dec(x_725);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_874 = !lean_is_exclusive(x_869);
if (x_874 == 0)
{
return x_869;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_869, 0);
x_876 = lean_ctor_get(x_869, 1);
lean_inc(x_876);
lean_inc(x_875);
lean_dec(x_869);
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_875);
lean_ctor_set(x_877, 1, x_876);
return x_877;
}
}
}
}
else
{
lean_object* x_878; 
lean_dec(x_707);
lean_dec(x_1);
x_878 = lean_box(0);
x_708 = x_878;
goto block_717;
}
block_717:
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_708);
x_709 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_710 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_710, 0, x_709);
x_711 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_711, 0, x_710);
x_712 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_713 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_711);
x_714 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_715 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
x_716 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_715, x_3, x_4, x_5, x_6, x_706);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_716;
}
}
case 6:
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_8, 1);
lean_inc(x_879);
lean_dec(x_8);
x_880 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16), 8, 1);
lean_closure_set(x_880, 0, x_1);
x_881 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_9, x_880, x_3, x_4, x_5, x_6, x_879);
return x_881;
}
case 7:
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_8, 1);
lean_inc(x_882);
lean_dec(x_8);
x_883 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_883) == 4)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_894 = lean_ctor_get(x_883, 0);
lean_inc(x_894);
lean_dec(x_883);
x_895 = lean_unsigned_to_nat(0u);
x_896 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_895);
x_897 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_896);
x_898 = lean_mk_array(x_896, x_897);
x_899 = lean_unsigned_to_nat(1u);
x_900 = lean_nat_sub(x_896, x_899);
lean_dec(x_896);
lean_inc(x_9);
x_901 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_898, x_900);
x_902 = lean_st_ref_get(x_6, x_882);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
lean_dec(x_902);
x_905 = lean_ctor_get(x_903, 0);
lean_inc(x_905);
lean_dec(x_903);
x_906 = lean_ctor_get(x_1, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_1, 2);
lean_inc(x_907);
x_908 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_907, x_905, x_894);
lean_dec(x_905);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; 
lean_inc(x_906);
x_909 = l_Lean_Name_append___main(x_894, x_906);
lean_inc(x_894);
x_910 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_894, x_3, x_4, x_5, x_6, x_904);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_911 = lean_ctor_get(x_910, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_910, 1);
lean_inc(x_912);
lean_dec(x_910);
x_913 = l_Lean_ConstantInfo_type(x_911);
x_914 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_913);
x_915 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_913, x_914, x_3, x_4, x_5, x_6, x_912);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_1006; uint8_t x_1007; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
x_1006 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1007 = l_Lean_Expr_isConstOf(x_916, x_1006);
if (x_1007 == 0)
{
lean_object* x_1008; uint8_t x_1009; 
x_1008 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1009 = l_Lean_Expr_isConstOf(x_916, x_1008);
lean_dec(x_916);
if (x_1009 == 0)
{
lean_object* x_1010; 
lean_dec(x_913);
lean_dec(x_911);
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_901);
lean_dec(x_894);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1010 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_917);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
lean_dec(x_1);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
x_1013 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1013, 0, x_906);
x_1014 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1015 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1015, 0, x_1014);
lean_ctor_set(x_1015, 1, x_1013);
x_1016 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1017 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1017, 0, x_1015);
lean_ctor_set(x_1017, 1, x_1016);
x_1018 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1019 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1019, 0, x_1018);
x_1020 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1020, 0, x_1019);
x_1021 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1021, 0, x_1017);
lean_ctor_set(x_1021, 1, x_1020);
x_1022 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1023 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1023, 0, x_1021);
lean_ctor_set(x_1023, 1, x_1022);
x_1024 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1023, x_3, x_4, x_5, x_6, x_1012);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1024;
}
else
{
lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_906);
lean_dec(x_9);
x_1025 = lean_ctor_get(x_1010, 1);
lean_inc(x_1025);
lean_dec(x_1010);
x_1026 = lean_ctor_get(x_1011, 0);
lean_inc(x_1026);
lean_dec(x_1011);
x_2 = x_1026;
x_7 = x_1025;
goto _start;
}
}
else
{
uint8_t x_1028; 
lean_dec(x_906);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1028 = !lean_is_exclusive(x_1010);
if (x_1028 == 0)
{
return x_1010;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1010, 0);
x_1030 = lean_ctor_get(x_1010, 1);
lean_inc(x_1030);
lean_inc(x_1029);
lean_dec(x_1010);
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
return x_1031;
}
}
}
else
{
lean_object* x_1032; 
x_1032 = lean_box(0);
x_918 = x_1032;
goto block_1005;
}
}
else
{
lean_object* x_1033; 
lean_dec(x_916);
x_1033 = lean_box(0);
x_918 = x_1033;
goto block_1005;
}
block_1005:
{
lean_object* x_919; 
lean_dec(x_918);
x_919 = l_Lean_ConstantInfo_value_x3f(x_911);
lean_dec(x_911);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
lean_dec(x_913);
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_901);
lean_dec(x_894);
lean_dec(x_1);
x_920 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_920, 0, x_906);
x_921 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_922 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_922, 1, x_920);
x_923 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_924 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_924, 0, x_922);
lean_ctor_set(x_924, 1, x_923);
x_925 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_926 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_926, 0, x_925);
x_927 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_927, 0, x_926);
x_928 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_928, 0, x_924);
lean_ctor_set(x_928, 1, x_927);
x_929 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_930 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_930, 0, x_928);
lean_ctor_set(x_930, 1, x_929);
x_931 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_930, x_3, x_4, x_5, x_6, x_917);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_931;
}
else
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_906);
lean_dec(x_9);
x_932 = lean_ctor_get(x_919, 0);
lean_inc(x_932);
lean_dec(x_919);
x_933 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_932);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_934 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_933, x_3, x_4, x_5, x_6, x_917);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_934, 1);
lean_inc(x_936);
lean_dec(x_934);
x_954 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_955 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed), 9, 2);
lean_closure_set(x_955, 0, x_1);
lean_closure_set(x_955, 1, x_954);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_956 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_913, x_955, x_3, x_4, x_5, x_6, x_936);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
x_959 = lean_box(0);
lean_inc(x_909);
x_960 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_960, 0, x_909);
lean_ctor_set(x_960, 1, x_959);
lean_ctor_set(x_960, 2, x_957);
x_961 = lean_box(0);
x_962 = 0;
x_963 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_963, 0, x_960);
lean_ctor_set(x_963, 1, x_935);
lean_ctor_set(x_963, 2, x_961);
lean_ctor_set_uint8(x_963, sizeof(void*)*3, x_962);
x_964 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_964, 0, x_963);
x_965 = lean_st_ref_get(x_6, x_958);
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = lean_ctor_get(x_966, 0);
lean_inc(x_968);
lean_dec(x_966);
x_969 = l_Lean_Environment_addAndCompile(x_968, x_959, x_964);
lean_dec(x_964);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_901);
lean_dec(x_894);
lean_dec(x_1);
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
lean_dec(x_969);
x_971 = l_Lean_KernelException_toMessageData(x_970, x_959);
x_972 = lean_ctor_get(x_5, 3);
lean_inc(x_972);
x_973 = l_Lean_MessageData_toString(x_971, x_967);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; 
lean_dec(x_972);
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec(x_973);
x_976 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_976, 0, x_974);
x_977 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_977, 0, x_976);
x_978 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_977, x_3, x_4, x_5, x_6, x_975);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_979 = !lean_is_exclusive(x_978);
if (x_979 == 0)
{
return x_978;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_980 = lean_ctor_get(x_978, 0);
x_981 = lean_ctor_get(x_978, 1);
lean_inc(x_981);
lean_inc(x_980);
lean_dec(x_978);
x_982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_982, 0, x_980);
lean_ctor_set(x_982, 1, x_981);
return x_982;
}
}
else
{
uint8_t x_983; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_983 = !lean_is_exclusive(x_973);
if (x_983 == 0)
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_984 = lean_ctor_get(x_973, 0);
x_985 = lean_io_error_to_string(x_984);
x_986 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_986, 0, x_985);
x_987 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_987, 0, x_986);
x_988 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_988, 0, x_972);
lean_ctor_set(x_988, 1, x_987);
lean_ctor_set(x_973, 0, x_988);
return x_973;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_989 = lean_ctor_get(x_973, 0);
x_990 = lean_ctor_get(x_973, 1);
lean_inc(x_990);
lean_inc(x_989);
lean_dec(x_973);
x_991 = lean_io_error_to_string(x_989);
x_992 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_992, 0, x_991);
x_993 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_993, 0, x_992);
x_994 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_994, 0, x_972);
lean_ctor_set(x_994, 1, x_993);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set(x_995, 1, x_990);
return x_995;
}
}
}
else
{
lean_object* x_996; 
x_996 = lean_ctor_get(x_969, 0);
lean_inc(x_996);
lean_dec(x_969);
x_937 = x_996;
x_938 = x_967;
goto block_953;
}
}
else
{
uint8_t x_997; 
lean_dec(x_935);
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_901);
lean_dec(x_894);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_997 = !lean_is_exclusive(x_956);
if (x_997 == 0)
{
return x_956;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_956, 0);
x_999 = lean_ctor_get(x_956, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_956);
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
return x_1000;
}
}
block_953:
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_inc(x_909);
x_939 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_907, x_937, x_894, x_909);
x_940 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_939, x_3, x_4, x_5, x_6, x_938);
x_941 = lean_ctor_get(x_940, 1);
lean_inc(x_941);
lean_dec(x_940);
x_942 = lean_box(0);
x_943 = l_Lean_mkConst(x_909, x_942);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_943);
x_944 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_943, x_3, x_4, x_5, x_6, x_941);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
x_947 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed), 11, 4);
lean_closure_set(x_947, 0, x_1);
lean_closure_set(x_947, 1, x_914);
lean_closure_set(x_947, 2, x_901);
lean_closure_set(x_947, 3, x_943);
x_948 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_945, x_947, x_3, x_4, x_5, x_6, x_946);
return x_948;
}
else
{
uint8_t x_949; 
lean_dec(x_943);
lean_dec(x_901);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_949 = !lean_is_exclusive(x_944);
if (x_949 == 0)
{
return x_944;
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_950 = lean_ctor_get(x_944, 0);
x_951 = lean_ctor_get(x_944, 1);
lean_inc(x_951);
lean_inc(x_950);
lean_dec(x_944);
x_952 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_952, 0, x_950);
lean_ctor_set(x_952, 1, x_951);
return x_952;
}
}
}
}
else
{
uint8_t x_1001; 
lean_dec(x_913);
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_901);
lean_dec(x_894);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1001 = !lean_is_exclusive(x_934);
if (x_1001 == 0)
{
return x_934;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_934, 0);
x_1003 = lean_ctor_get(x_934, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_934);
x_1004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
return x_1004;
}
}
}
}
}
else
{
uint8_t x_1034; 
lean_dec(x_913);
lean_dec(x_911);
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_906);
lean_dec(x_901);
lean_dec(x_894);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1034 = !lean_is_exclusive(x_915);
if (x_1034 == 0)
{
return x_915;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_915, 0);
x_1036 = lean_ctor_get(x_915, 1);
lean_inc(x_1036);
lean_inc(x_1035);
lean_dec(x_915);
x_1037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1037, 0, x_1035);
lean_ctor_set(x_1037, 1, x_1036);
return x_1037;
}
}
}
else
{
uint8_t x_1038; 
lean_dec(x_909);
lean_dec(x_907);
lean_dec(x_906);
lean_dec(x_901);
lean_dec(x_894);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1038 = !lean_is_exclusive(x_910);
if (x_1038 == 0)
{
return x_910;
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_910, 0);
x_1040 = lean_ctor_get(x_910, 1);
lean_inc(x_1040);
lean_inc(x_1039);
lean_dec(x_910);
x_1041 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1041, 0, x_1039);
lean_ctor_set(x_1041, 1, x_1040);
return x_1041;
}
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
lean_dec(x_907);
lean_dec(x_906);
lean_dec(x_894);
lean_dec(x_9);
x_1042 = lean_ctor_get(x_908, 0);
lean_inc(x_1042);
lean_dec(x_908);
x_1043 = lean_box(0);
x_1044 = l_Lean_mkConst(x_1042, x_1043);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1044);
x_1045 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1044, x_3, x_4, x_5, x_6, x_904);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1045, 1);
lean_inc(x_1047);
lean_dec(x_1045);
x_1048 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed), 10, 3);
lean_closure_set(x_1048, 0, x_1);
lean_closure_set(x_1048, 1, x_901);
lean_closure_set(x_1048, 2, x_1044);
x_1049 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1046, x_1048, x_3, x_4, x_5, x_6, x_1047);
return x_1049;
}
else
{
uint8_t x_1050; 
lean_dec(x_1044);
lean_dec(x_901);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1050 = !lean_is_exclusive(x_1045);
if (x_1050 == 0)
{
return x_1045;
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1051 = lean_ctor_get(x_1045, 0);
x_1052 = lean_ctor_get(x_1045, 1);
lean_inc(x_1052);
lean_inc(x_1051);
lean_dec(x_1045);
x_1053 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1053, 0, x_1051);
lean_ctor_set(x_1053, 1, x_1052);
return x_1053;
}
}
}
}
else
{
lean_object* x_1054; 
lean_dec(x_883);
lean_dec(x_1);
x_1054 = lean_box(0);
x_884 = x_1054;
goto block_893;
}
block_893:
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
lean_dec(x_884);
x_885 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_886 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_886, 0, x_885);
x_887 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_887, 0, x_886);
x_888 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_889 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_887);
x_890 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_891 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
x_892 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_891, x_3, x_4, x_5, x_6, x_882);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_892;
}
}
case 8:
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1055 = lean_ctor_get(x_8, 1);
lean_inc(x_1055);
lean_dec(x_8);
x_1056 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1056) == 4)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1067 = lean_ctor_get(x_1056, 0);
lean_inc(x_1067);
lean_dec(x_1056);
x_1068 = lean_unsigned_to_nat(0u);
x_1069 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1068);
x_1070 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1069);
x_1071 = lean_mk_array(x_1069, x_1070);
x_1072 = lean_unsigned_to_nat(1u);
x_1073 = lean_nat_sub(x_1069, x_1072);
lean_dec(x_1069);
lean_inc(x_9);
x_1074 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1071, x_1073);
x_1075 = lean_st_ref_get(x_6, x_1055);
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1075, 1);
lean_inc(x_1077);
lean_dec(x_1075);
x_1078 = lean_ctor_get(x_1076, 0);
lean_inc(x_1078);
lean_dec(x_1076);
x_1079 = lean_ctor_get(x_1, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1, 2);
lean_inc(x_1080);
x_1081 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1080, x_1078, x_1067);
lean_dec(x_1078);
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1082; lean_object* x_1083; 
lean_inc(x_1079);
x_1082 = l_Lean_Name_append___main(x_1067, x_1079);
lean_inc(x_1067);
x_1083 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1067, x_3, x_4, x_5, x_6, x_1077);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
lean_dec(x_1083);
x_1086 = l_Lean_ConstantInfo_type(x_1084);
x_1087 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1086);
x_1088 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1086, x_1087, x_3, x_4, x_5, x_6, x_1085);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1179; uint8_t x_1180; 
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
lean_dec(x_1088);
x_1179 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1180 = l_Lean_Expr_isConstOf(x_1089, x_1179);
if (x_1180 == 0)
{
lean_object* x_1181; uint8_t x_1182; 
x_1181 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1182 = l_Lean_Expr_isConstOf(x_1089, x_1181);
lean_dec(x_1089);
if (x_1182 == 0)
{
lean_object* x_1183; 
lean_dec(x_1086);
lean_dec(x_1084);
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1074);
lean_dec(x_1067);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1183 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_1090);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; 
x_1184 = lean_ctor_get(x_1183, 0);
lean_inc(x_1184);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
lean_dec(x_1);
x_1185 = lean_ctor_get(x_1183, 1);
lean_inc(x_1185);
lean_dec(x_1183);
x_1186 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1186, 0, x_1079);
x_1187 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1188 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1188, 0, x_1187);
lean_ctor_set(x_1188, 1, x_1186);
x_1189 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
x_1191 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1192, 0, x_1191);
x_1193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1193, 0, x_1192);
x_1194 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1194, 0, x_1190);
lean_ctor_set(x_1194, 1, x_1193);
x_1195 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1196 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1196, 0, x_1194);
lean_ctor_set(x_1196, 1, x_1195);
x_1197 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1196, x_3, x_4, x_5, x_6, x_1185);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1197;
}
else
{
lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1079);
lean_dec(x_9);
x_1198 = lean_ctor_get(x_1183, 1);
lean_inc(x_1198);
lean_dec(x_1183);
x_1199 = lean_ctor_get(x_1184, 0);
lean_inc(x_1199);
lean_dec(x_1184);
x_2 = x_1199;
x_7 = x_1198;
goto _start;
}
}
else
{
uint8_t x_1201; 
lean_dec(x_1079);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1201 = !lean_is_exclusive(x_1183);
if (x_1201 == 0)
{
return x_1183;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1202 = lean_ctor_get(x_1183, 0);
x_1203 = lean_ctor_get(x_1183, 1);
lean_inc(x_1203);
lean_inc(x_1202);
lean_dec(x_1183);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1202);
lean_ctor_set(x_1204, 1, x_1203);
return x_1204;
}
}
}
else
{
lean_object* x_1205; 
x_1205 = lean_box(0);
x_1091 = x_1205;
goto block_1178;
}
}
else
{
lean_object* x_1206; 
lean_dec(x_1089);
x_1206 = lean_box(0);
x_1091 = x_1206;
goto block_1178;
}
block_1178:
{
lean_object* x_1092; 
lean_dec(x_1091);
x_1092 = l_Lean_ConstantInfo_value_x3f(x_1084);
lean_dec(x_1084);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_1086);
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1074);
lean_dec(x_1067);
lean_dec(x_1);
x_1093 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1093, 0, x_1079);
x_1094 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1095 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1095, 0, x_1094);
lean_ctor_set(x_1095, 1, x_1093);
x_1096 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1097 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1097, 0, x_1095);
lean_ctor_set(x_1097, 1, x_1096);
x_1098 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1099 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1099, 0, x_1098);
x_1100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1100, 0, x_1099);
x_1101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1101, 0, x_1097);
lean_ctor_set(x_1101, 1, x_1100);
x_1102 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1103, 0, x_1101);
lean_ctor_set(x_1103, 1, x_1102);
x_1104 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1103, x_3, x_4, x_5, x_6, x_1090);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1104;
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
lean_dec(x_1079);
lean_dec(x_9);
x_1105 = lean_ctor_get(x_1092, 0);
lean_inc(x_1105);
lean_dec(x_1092);
x_1106 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1105);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1107 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1106, x_3, x_4, x_5, x_6, x_1090);
if (lean_obj_tag(x_1107) == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1108 = lean_ctor_get(x_1107, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1107, 1);
lean_inc(x_1109);
lean_dec(x_1107);
x_1127 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1128 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed), 9, 2);
lean_closure_set(x_1128, 0, x_1);
lean_closure_set(x_1128, 1, x_1127);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1129 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1086, x_1128, x_3, x_4, x_5, x_6, x_1109);
if (lean_obj_tag(x_1129) == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; uint8_t x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1130 = lean_ctor_get(x_1129, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1129, 1);
lean_inc(x_1131);
lean_dec(x_1129);
x_1132 = lean_box(0);
lean_inc(x_1082);
x_1133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1133, 0, x_1082);
lean_ctor_set(x_1133, 1, x_1132);
lean_ctor_set(x_1133, 2, x_1130);
x_1134 = lean_box(0);
x_1135 = 0;
x_1136 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1136, 0, x_1133);
lean_ctor_set(x_1136, 1, x_1108);
lean_ctor_set(x_1136, 2, x_1134);
lean_ctor_set_uint8(x_1136, sizeof(void*)*3, x_1135);
x_1137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1137, 0, x_1136);
x_1138 = lean_st_ref_get(x_6, x_1131);
x_1139 = lean_ctor_get(x_1138, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1138, 1);
lean_inc(x_1140);
lean_dec(x_1138);
x_1141 = lean_ctor_get(x_1139, 0);
lean_inc(x_1141);
lean_dec(x_1139);
x_1142 = l_Lean_Environment_addAndCompile(x_1141, x_1132, x_1137);
lean_dec(x_1137);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1074);
lean_dec(x_1067);
lean_dec(x_1);
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
lean_dec(x_1142);
x_1144 = l_Lean_KernelException_toMessageData(x_1143, x_1132);
x_1145 = lean_ctor_get(x_5, 3);
lean_inc(x_1145);
x_1146 = l_Lean_MessageData_toString(x_1144, x_1140);
if (lean_obj_tag(x_1146) == 0)
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; uint8_t x_1152; 
lean_dec(x_1145);
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1146, 1);
lean_inc(x_1148);
lean_dec(x_1146);
x_1149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1149, 0, x_1147);
x_1150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1150, 0, x_1149);
x_1151 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1150, x_3, x_4, x_5, x_6, x_1148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1152 = !lean_is_exclusive(x_1151);
if (x_1152 == 0)
{
return x_1151;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1153 = lean_ctor_get(x_1151, 0);
x_1154 = lean_ctor_get(x_1151, 1);
lean_inc(x_1154);
lean_inc(x_1153);
lean_dec(x_1151);
x_1155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
return x_1155;
}
}
else
{
uint8_t x_1156; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1156 = !lean_is_exclusive(x_1146);
if (x_1156 == 0)
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1157 = lean_ctor_get(x_1146, 0);
x_1158 = lean_io_error_to_string(x_1157);
x_1159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1159, 0, x_1158);
x_1160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1160, 0, x_1159);
x_1161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1161, 0, x_1145);
lean_ctor_set(x_1161, 1, x_1160);
lean_ctor_set(x_1146, 0, x_1161);
return x_1146;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1162 = lean_ctor_get(x_1146, 0);
x_1163 = lean_ctor_get(x_1146, 1);
lean_inc(x_1163);
lean_inc(x_1162);
lean_dec(x_1146);
x_1164 = lean_io_error_to_string(x_1162);
x_1165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1165, 0, x_1164);
x_1166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1166, 0, x_1165);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_1145);
lean_ctor_set(x_1167, 1, x_1166);
x_1168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1168, 0, x_1167);
lean_ctor_set(x_1168, 1, x_1163);
return x_1168;
}
}
}
else
{
lean_object* x_1169; 
x_1169 = lean_ctor_get(x_1142, 0);
lean_inc(x_1169);
lean_dec(x_1142);
x_1110 = x_1169;
x_1111 = x_1140;
goto block_1126;
}
}
else
{
uint8_t x_1170; 
lean_dec(x_1108);
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1074);
lean_dec(x_1067);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1170 = !lean_is_exclusive(x_1129);
if (x_1170 == 0)
{
return x_1129;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1171 = lean_ctor_get(x_1129, 0);
x_1172 = lean_ctor_get(x_1129, 1);
lean_inc(x_1172);
lean_inc(x_1171);
lean_dec(x_1129);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1171);
lean_ctor_set(x_1173, 1, x_1172);
return x_1173;
}
}
block_1126:
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
lean_inc(x_1082);
x_1112 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1080, x_1110, x_1067, x_1082);
x_1113 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_1112, x_3, x_4, x_5, x_6, x_1111);
x_1114 = lean_ctor_get(x_1113, 1);
lean_inc(x_1114);
lean_dec(x_1113);
x_1115 = lean_box(0);
x_1116 = l_Lean_mkConst(x_1082, x_1115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1116);
x_1117 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1116, x_3, x_4, x_5, x_6, x_1114);
if (lean_obj_tag(x_1117) == 0)
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1118 = lean_ctor_get(x_1117, 0);
lean_inc(x_1118);
x_1119 = lean_ctor_get(x_1117, 1);
lean_inc(x_1119);
lean_dec(x_1117);
x_1120 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed), 11, 4);
lean_closure_set(x_1120, 0, x_1);
lean_closure_set(x_1120, 1, x_1087);
lean_closure_set(x_1120, 2, x_1074);
lean_closure_set(x_1120, 3, x_1116);
x_1121 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1118, x_1120, x_3, x_4, x_5, x_6, x_1119);
return x_1121;
}
else
{
uint8_t x_1122; 
lean_dec(x_1116);
lean_dec(x_1074);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1122 = !lean_is_exclusive(x_1117);
if (x_1122 == 0)
{
return x_1117;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_1117, 0);
x_1124 = lean_ctor_get(x_1117, 1);
lean_inc(x_1124);
lean_inc(x_1123);
lean_dec(x_1117);
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
return x_1125;
}
}
}
}
else
{
uint8_t x_1174; 
lean_dec(x_1086);
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1074);
lean_dec(x_1067);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1174 = !lean_is_exclusive(x_1107);
if (x_1174 == 0)
{
return x_1107;
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
x_1175 = lean_ctor_get(x_1107, 0);
x_1176 = lean_ctor_get(x_1107, 1);
lean_inc(x_1176);
lean_inc(x_1175);
lean_dec(x_1107);
x_1177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1177, 0, x_1175);
lean_ctor_set(x_1177, 1, x_1176);
return x_1177;
}
}
}
}
}
else
{
uint8_t x_1207; 
lean_dec(x_1086);
lean_dec(x_1084);
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1074);
lean_dec(x_1067);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1207 = !lean_is_exclusive(x_1088);
if (x_1207 == 0)
{
return x_1088;
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
x_1208 = lean_ctor_get(x_1088, 0);
x_1209 = lean_ctor_get(x_1088, 1);
lean_inc(x_1209);
lean_inc(x_1208);
lean_dec(x_1088);
x_1210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1210, 0, x_1208);
lean_ctor_set(x_1210, 1, x_1209);
return x_1210;
}
}
}
else
{
uint8_t x_1211; 
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1074);
lean_dec(x_1067);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1211 = !lean_is_exclusive(x_1083);
if (x_1211 == 0)
{
return x_1083;
}
else
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
x_1212 = lean_ctor_get(x_1083, 0);
x_1213 = lean_ctor_get(x_1083, 1);
lean_inc(x_1213);
lean_inc(x_1212);
lean_dec(x_1083);
x_1214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1214, 0, x_1212);
lean_ctor_set(x_1214, 1, x_1213);
return x_1214;
}
}
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1067);
lean_dec(x_9);
x_1215 = lean_ctor_get(x_1081, 0);
lean_inc(x_1215);
lean_dec(x_1081);
x_1216 = lean_box(0);
x_1217 = l_Lean_mkConst(x_1215, x_1216);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1217);
x_1218 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1217, x_3, x_4, x_5, x_6, x_1077);
if (lean_obj_tag(x_1218) == 0)
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
x_1219 = lean_ctor_get(x_1218, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1218, 1);
lean_inc(x_1220);
lean_dec(x_1218);
x_1221 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed), 10, 3);
lean_closure_set(x_1221, 0, x_1);
lean_closure_set(x_1221, 1, x_1074);
lean_closure_set(x_1221, 2, x_1217);
x_1222 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1219, x_1221, x_3, x_4, x_5, x_6, x_1220);
return x_1222;
}
else
{
uint8_t x_1223; 
lean_dec(x_1217);
lean_dec(x_1074);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1223 = !lean_is_exclusive(x_1218);
if (x_1223 == 0)
{
return x_1218;
}
else
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1224 = lean_ctor_get(x_1218, 0);
x_1225 = lean_ctor_get(x_1218, 1);
lean_inc(x_1225);
lean_inc(x_1224);
lean_dec(x_1218);
x_1226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1226, 0, x_1224);
lean_ctor_set(x_1226, 1, x_1225);
return x_1226;
}
}
}
}
else
{
lean_object* x_1227; 
lean_dec(x_1056);
lean_dec(x_1);
x_1227 = lean_box(0);
x_1057 = x_1227;
goto block_1066;
}
block_1066:
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1057);
x_1058 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1059 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1059, 0, x_1058);
x_1060 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1060, 0, x_1059);
x_1061 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1062 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_1060);
x_1063 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1064 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
x_1065 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1064, x_3, x_4, x_5, x_6, x_1055);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1065;
}
}
case 9:
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1228 = lean_ctor_get(x_8, 1);
lean_inc(x_1228);
lean_dec(x_8);
x_1229 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1229) == 4)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
x_1240 = lean_ctor_get(x_1229, 0);
lean_inc(x_1240);
lean_dec(x_1229);
x_1241 = lean_unsigned_to_nat(0u);
x_1242 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1241);
x_1243 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1242);
x_1244 = lean_mk_array(x_1242, x_1243);
x_1245 = lean_unsigned_to_nat(1u);
x_1246 = lean_nat_sub(x_1242, x_1245);
lean_dec(x_1242);
lean_inc(x_9);
x_1247 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1244, x_1246);
x_1248 = lean_st_ref_get(x_6, x_1228);
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1248, 1);
lean_inc(x_1250);
lean_dec(x_1248);
x_1251 = lean_ctor_get(x_1249, 0);
lean_inc(x_1251);
lean_dec(x_1249);
x_1252 = lean_ctor_get(x_1, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1, 2);
lean_inc(x_1253);
x_1254 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1253, x_1251, x_1240);
lean_dec(x_1251);
if (lean_obj_tag(x_1254) == 0)
{
lean_object* x_1255; lean_object* x_1256; 
lean_inc(x_1252);
x_1255 = l_Lean_Name_append___main(x_1240, x_1252);
lean_inc(x_1240);
x_1256 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1240, x_3, x_4, x_5, x_6, x_1250);
if (lean_obj_tag(x_1256) == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1256, 1);
lean_inc(x_1258);
lean_dec(x_1256);
x_1259 = l_Lean_ConstantInfo_type(x_1257);
x_1260 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1259);
x_1261 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1259, x_1260, x_3, x_4, x_5, x_6, x_1258);
if (lean_obj_tag(x_1261) == 0)
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1352; uint8_t x_1353; 
x_1262 = lean_ctor_get(x_1261, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1261, 1);
lean_inc(x_1263);
lean_dec(x_1261);
x_1352 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1353 = l_Lean_Expr_isConstOf(x_1262, x_1352);
if (x_1353 == 0)
{
lean_object* x_1354; uint8_t x_1355; 
x_1354 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1355 = l_Lean_Expr_isConstOf(x_1262, x_1354);
lean_dec(x_1262);
if (x_1355 == 0)
{
lean_object* x_1356; 
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1247);
lean_dec(x_1240);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1356 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_1263);
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1357; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
if (lean_obj_tag(x_1357) == 0)
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
lean_dec(x_1);
x_1358 = lean_ctor_get(x_1356, 1);
lean_inc(x_1358);
lean_dec(x_1356);
x_1359 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1359, 0, x_1252);
x_1360 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1361 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1361, 0, x_1360);
lean_ctor_set(x_1361, 1, x_1359);
x_1362 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1363 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1363, 0, x_1361);
lean_ctor_set(x_1363, 1, x_1362);
x_1364 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1365 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1365, 0, x_1364);
x_1366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1366, 0, x_1365);
x_1367 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1367, 0, x_1363);
lean_ctor_set(x_1367, 1, x_1366);
x_1368 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1369 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1369, 0, x_1367);
lean_ctor_set(x_1369, 1, x_1368);
x_1370 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1369, x_3, x_4, x_5, x_6, x_1358);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1370;
}
else
{
lean_object* x_1371; lean_object* x_1372; 
lean_dec(x_1252);
lean_dec(x_9);
x_1371 = lean_ctor_get(x_1356, 1);
lean_inc(x_1371);
lean_dec(x_1356);
x_1372 = lean_ctor_get(x_1357, 0);
lean_inc(x_1372);
lean_dec(x_1357);
x_2 = x_1372;
x_7 = x_1371;
goto _start;
}
}
else
{
uint8_t x_1374; 
lean_dec(x_1252);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1374 = !lean_is_exclusive(x_1356);
if (x_1374 == 0)
{
return x_1356;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1356, 0);
x_1376 = lean_ctor_get(x_1356, 1);
lean_inc(x_1376);
lean_inc(x_1375);
lean_dec(x_1356);
x_1377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1377, 0, x_1375);
lean_ctor_set(x_1377, 1, x_1376);
return x_1377;
}
}
}
else
{
lean_object* x_1378; 
x_1378 = lean_box(0);
x_1264 = x_1378;
goto block_1351;
}
}
else
{
lean_object* x_1379; 
lean_dec(x_1262);
x_1379 = lean_box(0);
x_1264 = x_1379;
goto block_1351;
}
block_1351:
{
lean_object* x_1265; 
lean_dec(x_1264);
x_1265 = l_Lean_ConstantInfo_value_x3f(x_1257);
lean_dec(x_1257);
if (lean_obj_tag(x_1265) == 0)
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
lean_dec(x_1259);
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1247);
lean_dec(x_1240);
lean_dec(x_1);
x_1266 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1266, 0, x_1252);
x_1267 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1268 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1268, 0, x_1267);
lean_ctor_set(x_1268, 1, x_1266);
x_1269 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1270 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
x_1271 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1272 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1272, 0, x_1271);
x_1273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1273, 0, x_1272);
x_1274 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1274, 0, x_1270);
lean_ctor_set(x_1274, 1, x_1273);
x_1275 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1276 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1276, 0, x_1274);
lean_ctor_set(x_1276, 1, x_1275);
x_1277 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1276, x_3, x_4, x_5, x_6, x_1263);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1277;
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_1252);
lean_dec(x_9);
x_1278 = lean_ctor_get(x_1265, 0);
lean_inc(x_1278);
lean_dec(x_1265);
x_1279 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1278);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1280 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1279, x_3, x_4, x_5, x_6, x_1263);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1280, 1);
lean_inc(x_1282);
lean_dec(x_1280);
x_1300 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1301 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed), 9, 2);
lean_closure_set(x_1301, 0, x_1);
lean_closure_set(x_1301, 1, x_1300);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1302 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1259, x_1301, x_3, x_4, x_5, x_6, x_1282);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec(x_1302);
x_1305 = lean_box(0);
lean_inc(x_1255);
x_1306 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1306, 0, x_1255);
lean_ctor_set(x_1306, 1, x_1305);
lean_ctor_set(x_1306, 2, x_1303);
x_1307 = lean_box(0);
x_1308 = 0;
x_1309 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1309, 0, x_1306);
lean_ctor_set(x_1309, 1, x_1281);
lean_ctor_set(x_1309, 2, x_1307);
lean_ctor_set_uint8(x_1309, sizeof(void*)*3, x_1308);
x_1310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1310, 0, x_1309);
x_1311 = lean_st_ref_get(x_6, x_1304);
x_1312 = lean_ctor_get(x_1311, 0);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1311, 1);
lean_inc(x_1313);
lean_dec(x_1311);
x_1314 = lean_ctor_get(x_1312, 0);
lean_inc(x_1314);
lean_dec(x_1312);
x_1315 = l_Lean_Environment_addAndCompile(x_1314, x_1305, x_1310);
lean_dec(x_1310);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1247);
lean_dec(x_1240);
lean_dec(x_1);
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
lean_dec(x_1315);
x_1317 = l_Lean_KernelException_toMessageData(x_1316, x_1305);
x_1318 = lean_ctor_get(x_5, 3);
lean_inc(x_1318);
x_1319 = l_Lean_MessageData_toString(x_1317, x_1313);
if (lean_obj_tag(x_1319) == 0)
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint8_t x_1325; 
lean_dec(x_1318);
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1319, 1);
lean_inc(x_1321);
lean_dec(x_1319);
x_1322 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1322, 0, x_1320);
x_1323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1323, 0, x_1322);
x_1324 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1323, x_3, x_4, x_5, x_6, x_1321);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1325 = !lean_is_exclusive(x_1324);
if (x_1325 == 0)
{
return x_1324;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
x_1326 = lean_ctor_get(x_1324, 0);
x_1327 = lean_ctor_get(x_1324, 1);
lean_inc(x_1327);
lean_inc(x_1326);
lean_dec(x_1324);
x_1328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1328, 0, x_1326);
lean_ctor_set(x_1328, 1, x_1327);
return x_1328;
}
}
else
{
uint8_t x_1329; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1329 = !lean_is_exclusive(x_1319);
if (x_1329 == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
x_1330 = lean_ctor_get(x_1319, 0);
x_1331 = lean_io_error_to_string(x_1330);
x_1332 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1332, 0, x_1331);
x_1333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1333, 0, x_1332);
x_1334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1334, 0, x_1318);
lean_ctor_set(x_1334, 1, x_1333);
lean_ctor_set(x_1319, 0, x_1334);
return x_1319;
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1335 = lean_ctor_get(x_1319, 0);
x_1336 = lean_ctor_get(x_1319, 1);
lean_inc(x_1336);
lean_inc(x_1335);
lean_dec(x_1319);
x_1337 = lean_io_error_to_string(x_1335);
x_1338 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1338, 0, x_1337);
x_1339 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1339, 0, x_1338);
x_1340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1340, 0, x_1318);
lean_ctor_set(x_1340, 1, x_1339);
x_1341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1341, 0, x_1340);
lean_ctor_set(x_1341, 1, x_1336);
return x_1341;
}
}
}
else
{
lean_object* x_1342; 
x_1342 = lean_ctor_get(x_1315, 0);
lean_inc(x_1342);
lean_dec(x_1315);
x_1283 = x_1342;
x_1284 = x_1313;
goto block_1299;
}
}
else
{
uint8_t x_1343; 
lean_dec(x_1281);
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1247);
lean_dec(x_1240);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1343 = !lean_is_exclusive(x_1302);
if (x_1343 == 0)
{
return x_1302;
}
else
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
x_1344 = lean_ctor_get(x_1302, 0);
x_1345 = lean_ctor_get(x_1302, 1);
lean_inc(x_1345);
lean_inc(x_1344);
lean_dec(x_1302);
x_1346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1346, 0, x_1344);
lean_ctor_set(x_1346, 1, x_1345);
return x_1346;
}
}
block_1299:
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
lean_inc(x_1255);
x_1285 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1253, x_1283, x_1240, x_1255);
x_1286 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_1285, x_3, x_4, x_5, x_6, x_1284);
x_1287 = lean_ctor_get(x_1286, 1);
lean_inc(x_1287);
lean_dec(x_1286);
x_1288 = lean_box(0);
x_1289 = l_Lean_mkConst(x_1255, x_1288);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1289);
x_1290 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1289, x_3, x_4, x_5, x_6, x_1287);
if (lean_obj_tag(x_1290) == 0)
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1291 = lean_ctor_get(x_1290, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1290, 1);
lean_inc(x_1292);
lean_dec(x_1290);
x_1293 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed), 11, 4);
lean_closure_set(x_1293, 0, x_1);
lean_closure_set(x_1293, 1, x_1260);
lean_closure_set(x_1293, 2, x_1247);
lean_closure_set(x_1293, 3, x_1289);
x_1294 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1291, x_1293, x_3, x_4, x_5, x_6, x_1292);
return x_1294;
}
else
{
uint8_t x_1295; 
lean_dec(x_1289);
lean_dec(x_1247);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1295 = !lean_is_exclusive(x_1290);
if (x_1295 == 0)
{
return x_1290;
}
else
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
x_1296 = lean_ctor_get(x_1290, 0);
x_1297 = lean_ctor_get(x_1290, 1);
lean_inc(x_1297);
lean_inc(x_1296);
lean_dec(x_1290);
x_1298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1298, 0, x_1296);
lean_ctor_set(x_1298, 1, x_1297);
return x_1298;
}
}
}
}
else
{
uint8_t x_1347; 
lean_dec(x_1259);
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1247);
lean_dec(x_1240);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1347 = !lean_is_exclusive(x_1280);
if (x_1347 == 0)
{
return x_1280;
}
else
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1348 = lean_ctor_get(x_1280, 0);
x_1349 = lean_ctor_get(x_1280, 1);
lean_inc(x_1349);
lean_inc(x_1348);
lean_dec(x_1280);
x_1350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1350, 0, x_1348);
lean_ctor_set(x_1350, 1, x_1349);
return x_1350;
}
}
}
}
}
else
{
uint8_t x_1380; 
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1252);
lean_dec(x_1247);
lean_dec(x_1240);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1380 = !lean_is_exclusive(x_1261);
if (x_1380 == 0)
{
return x_1261;
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
x_1381 = lean_ctor_get(x_1261, 0);
x_1382 = lean_ctor_get(x_1261, 1);
lean_inc(x_1382);
lean_inc(x_1381);
lean_dec(x_1261);
x_1383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1383, 0, x_1381);
lean_ctor_set(x_1383, 1, x_1382);
return x_1383;
}
}
}
else
{
uint8_t x_1384; 
lean_dec(x_1255);
lean_dec(x_1253);
lean_dec(x_1252);
lean_dec(x_1247);
lean_dec(x_1240);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1384 = !lean_is_exclusive(x_1256);
if (x_1384 == 0)
{
return x_1256;
}
else
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1256, 0);
x_1386 = lean_ctor_get(x_1256, 1);
lean_inc(x_1386);
lean_inc(x_1385);
lean_dec(x_1256);
x_1387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1387, 0, x_1385);
lean_ctor_set(x_1387, 1, x_1386);
return x_1387;
}
}
}
else
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
lean_dec(x_1253);
lean_dec(x_1252);
lean_dec(x_1240);
lean_dec(x_9);
x_1388 = lean_ctor_get(x_1254, 0);
lean_inc(x_1388);
lean_dec(x_1254);
x_1389 = lean_box(0);
x_1390 = l_Lean_mkConst(x_1388, x_1389);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1390);
x_1391 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1390, x_3, x_4, x_5, x_6, x_1250);
if (lean_obj_tag(x_1391) == 0)
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1391, 1);
lean_inc(x_1393);
lean_dec(x_1391);
x_1394 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed), 10, 3);
lean_closure_set(x_1394, 0, x_1);
lean_closure_set(x_1394, 1, x_1247);
lean_closure_set(x_1394, 2, x_1390);
x_1395 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1392, x_1394, x_3, x_4, x_5, x_6, x_1393);
return x_1395;
}
else
{
uint8_t x_1396; 
lean_dec(x_1390);
lean_dec(x_1247);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1396 = !lean_is_exclusive(x_1391);
if (x_1396 == 0)
{
return x_1391;
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1397 = lean_ctor_get(x_1391, 0);
x_1398 = lean_ctor_get(x_1391, 1);
lean_inc(x_1398);
lean_inc(x_1397);
lean_dec(x_1391);
x_1399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
return x_1399;
}
}
}
}
else
{
lean_object* x_1400; 
lean_dec(x_1229);
lean_dec(x_1);
x_1400 = lean_box(0);
x_1230 = x_1400;
goto block_1239;
}
block_1239:
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
lean_dec(x_1230);
x_1231 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1232 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1232, 0, x_1231);
x_1233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1233, 0, x_1232);
x_1234 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1233);
x_1236 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1237, 0, x_1235);
lean_ctor_set(x_1237, 1, x_1236);
x_1238 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1237, x_3, x_4, x_5, x_6, x_1228);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1238;
}
}
case 10:
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_8, 1);
lean_inc(x_1401);
lean_dec(x_8);
x_1402 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1402) == 4)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; 
x_1413 = lean_ctor_get(x_1402, 0);
lean_inc(x_1413);
lean_dec(x_1402);
x_1414 = lean_unsigned_to_nat(0u);
x_1415 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1414);
x_1416 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1415);
x_1417 = lean_mk_array(x_1415, x_1416);
x_1418 = lean_unsigned_to_nat(1u);
x_1419 = lean_nat_sub(x_1415, x_1418);
lean_dec(x_1415);
lean_inc(x_9);
x_1420 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1417, x_1419);
x_1421 = lean_st_ref_get(x_6, x_1401);
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1421, 1);
lean_inc(x_1423);
lean_dec(x_1421);
x_1424 = lean_ctor_get(x_1422, 0);
lean_inc(x_1424);
lean_dec(x_1422);
x_1425 = lean_ctor_get(x_1, 0);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_1, 2);
lean_inc(x_1426);
x_1427 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1426, x_1424, x_1413);
lean_dec(x_1424);
if (lean_obj_tag(x_1427) == 0)
{
lean_object* x_1428; lean_object* x_1429; 
lean_inc(x_1425);
x_1428 = l_Lean_Name_append___main(x_1413, x_1425);
lean_inc(x_1413);
x_1429 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1413, x_3, x_4, x_5, x_6, x_1423);
if (lean_obj_tag(x_1429) == 0)
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; 
x_1430 = lean_ctor_get(x_1429, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1429, 1);
lean_inc(x_1431);
lean_dec(x_1429);
x_1432 = l_Lean_ConstantInfo_type(x_1430);
x_1433 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1432);
x_1434 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1432, x_1433, x_3, x_4, x_5, x_6, x_1431);
if (lean_obj_tag(x_1434) == 0)
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1525; uint8_t x_1526; 
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1434, 1);
lean_inc(x_1436);
lean_dec(x_1434);
x_1525 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1526 = l_Lean_Expr_isConstOf(x_1435, x_1525);
if (x_1526 == 0)
{
lean_object* x_1527; uint8_t x_1528; 
x_1527 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1528 = l_Lean_Expr_isConstOf(x_1435, x_1527);
lean_dec(x_1435);
if (x_1528 == 0)
{
lean_object* x_1529; 
lean_dec(x_1432);
lean_dec(x_1430);
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1420);
lean_dec(x_1413);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1529 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_1436);
if (lean_obj_tag(x_1529) == 0)
{
lean_object* x_1530; 
x_1530 = lean_ctor_get(x_1529, 0);
lean_inc(x_1530);
if (lean_obj_tag(x_1530) == 0)
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
lean_dec(x_1);
x_1531 = lean_ctor_get(x_1529, 1);
lean_inc(x_1531);
lean_dec(x_1529);
x_1532 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1532, 0, x_1425);
x_1533 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1534 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set(x_1534, 1, x_1532);
x_1535 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1536 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1536, 0, x_1534);
lean_ctor_set(x_1536, 1, x_1535);
x_1537 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1538 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1538, 0, x_1537);
x_1539 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1539, 0, x_1538);
x_1540 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1540, 0, x_1536);
lean_ctor_set(x_1540, 1, x_1539);
x_1541 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1542 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1542, 0, x_1540);
lean_ctor_set(x_1542, 1, x_1541);
x_1543 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1542, x_3, x_4, x_5, x_6, x_1531);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1543;
}
else
{
lean_object* x_1544; lean_object* x_1545; 
lean_dec(x_1425);
lean_dec(x_9);
x_1544 = lean_ctor_get(x_1529, 1);
lean_inc(x_1544);
lean_dec(x_1529);
x_1545 = lean_ctor_get(x_1530, 0);
lean_inc(x_1545);
lean_dec(x_1530);
x_2 = x_1545;
x_7 = x_1544;
goto _start;
}
}
else
{
uint8_t x_1547; 
lean_dec(x_1425);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1547 = !lean_is_exclusive(x_1529);
if (x_1547 == 0)
{
return x_1529;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
x_1548 = lean_ctor_get(x_1529, 0);
x_1549 = lean_ctor_get(x_1529, 1);
lean_inc(x_1549);
lean_inc(x_1548);
lean_dec(x_1529);
x_1550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1550, 0, x_1548);
lean_ctor_set(x_1550, 1, x_1549);
return x_1550;
}
}
}
else
{
lean_object* x_1551; 
x_1551 = lean_box(0);
x_1437 = x_1551;
goto block_1524;
}
}
else
{
lean_object* x_1552; 
lean_dec(x_1435);
x_1552 = lean_box(0);
x_1437 = x_1552;
goto block_1524;
}
block_1524:
{
lean_object* x_1438; 
lean_dec(x_1437);
x_1438 = l_Lean_ConstantInfo_value_x3f(x_1430);
lean_dec(x_1430);
if (lean_obj_tag(x_1438) == 0)
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
lean_dec(x_1432);
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1420);
lean_dec(x_1413);
lean_dec(x_1);
x_1439 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1439, 0, x_1425);
x_1440 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1441 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1441, 0, x_1440);
lean_ctor_set(x_1441, 1, x_1439);
x_1442 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1443 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1443, 0, x_1441);
lean_ctor_set(x_1443, 1, x_1442);
x_1444 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1445 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1445, 0, x_1444);
x_1446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1446, 0, x_1445);
x_1447 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1447, 0, x_1443);
lean_ctor_set(x_1447, 1, x_1446);
x_1448 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1449 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1449, 0, x_1447);
lean_ctor_set(x_1449, 1, x_1448);
x_1450 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1449, x_3, x_4, x_5, x_6, x_1436);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1450;
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_1425);
lean_dec(x_9);
x_1451 = lean_ctor_get(x_1438, 0);
lean_inc(x_1451);
lean_dec(x_1438);
x_1452 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1451);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1453 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1452, x_3, x_4, x_5, x_6, x_1436);
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
x_1454 = lean_ctor_get(x_1453, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1453, 1);
lean_inc(x_1455);
lean_dec(x_1453);
x_1473 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1474 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed), 9, 2);
lean_closure_set(x_1474, 0, x_1);
lean_closure_set(x_1474, 1, x_1473);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1475 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1432, x_1474, x_3, x_4, x_5, x_6, x_1455);
if (lean_obj_tag(x_1475) == 0)
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; uint8_t x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
x_1476 = lean_ctor_get(x_1475, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1475, 1);
lean_inc(x_1477);
lean_dec(x_1475);
x_1478 = lean_box(0);
lean_inc(x_1428);
x_1479 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1479, 0, x_1428);
lean_ctor_set(x_1479, 1, x_1478);
lean_ctor_set(x_1479, 2, x_1476);
x_1480 = lean_box(0);
x_1481 = 0;
x_1482 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1482, 0, x_1479);
lean_ctor_set(x_1482, 1, x_1454);
lean_ctor_set(x_1482, 2, x_1480);
lean_ctor_set_uint8(x_1482, sizeof(void*)*3, x_1481);
x_1483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1483, 0, x_1482);
x_1484 = lean_st_ref_get(x_6, x_1477);
x_1485 = lean_ctor_get(x_1484, 0);
lean_inc(x_1485);
x_1486 = lean_ctor_get(x_1484, 1);
lean_inc(x_1486);
lean_dec(x_1484);
x_1487 = lean_ctor_get(x_1485, 0);
lean_inc(x_1487);
lean_dec(x_1485);
x_1488 = l_Lean_Environment_addAndCompile(x_1487, x_1478, x_1483);
lean_dec(x_1483);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; 
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1420);
lean_dec(x_1413);
lean_dec(x_1);
x_1489 = lean_ctor_get(x_1488, 0);
lean_inc(x_1489);
lean_dec(x_1488);
x_1490 = l_Lean_KernelException_toMessageData(x_1489, x_1478);
x_1491 = lean_ctor_get(x_5, 3);
lean_inc(x_1491);
x_1492 = l_Lean_MessageData_toString(x_1490, x_1486);
if (lean_obj_tag(x_1492) == 0)
{
lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; uint8_t x_1498; 
lean_dec(x_1491);
x_1493 = lean_ctor_get(x_1492, 0);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1492, 1);
lean_inc(x_1494);
lean_dec(x_1492);
x_1495 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1495, 0, x_1493);
x_1496 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1496, 0, x_1495);
x_1497 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1496, x_3, x_4, x_5, x_6, x_1494);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1498 = !lean_is_exclusive(x_1497);
if (x_1498 == 0)
{
return x_1497;
}
else
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
x_1499 = lean_ctor_get(x_1497, 0);
x_1500 = lean_ctor_get(x_1497, 1);
lean_inc(x_1500);
lean_inc(x_1499);
lean_dec(x_1497);
x_1501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1501, 0, x_1499);
lean_ctor_set(x_1501, 1, x_1500);
return x_1501;
}
}
else
{
uint8_t x_1502; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1502 = !lean_is_exclusive(x_1492);
if (x_1502 == 0)
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; 
x_1503 = lean_ctor_get(x_1492, 0);
x_1504 = lean_io_error_to_string(x_1503);
x_1505 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1505, 0, x_1504);
x_1506 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1506, 0, x_1505);
x_1507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1507, 0, x_1491);
lean_ctor_set(x_1507, 1, x_1506);
lean_ctor_set(x_1492, 0, x_1507);
return x_1492;
}
else
{
lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
x_1508 = lean_ctor_get(x_1492, 0);
x_1509 = lean_ctor_get(x_1492, 1);
lean_inc(x_1509);
lean_inc(x_1508);
lean_dec(x_1492);
x_1510 = lean_io_error_to_string(x_1508);
x_1511 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1511, 0, x_1510);
x_1512 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1512, 0, x_1511);
x_1513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1513, 0, x_1491);
lean_ctor_set(x_1513, 1, x_1512);
x_1514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1514, 0, x_1513);
lean_ctor_set(x_1514, 1, x_1509);
return x_1514;
}
}
}
else
{
lean_object* x_1515; 
x_1515 = lean_ctor_get(x_1488, 0);
lean_inc(x_1515);
lean_dec(x_1488);
x_1456 = x_1515;
x_1457 = x_1486;
goto block_1472;
}
}
else
{
uint8_t x_1516; 
lean_dec(x_1454);
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1420);
lean_dec(x_1413);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1516 = !lean_is_exclusive(x_1475);
if (x_1516 == 0)
{
return x_1475;
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1517 = lean_ctor_get(x_1475, 0);
x_1518 = lean_ctor_get(x_1475, 1);
lean_inc(x_1518);
lean_inc(x_1517);
lean_dec(x_1475);
x_1519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1519, 0, x_1517);
lean_ctor_set(x_1519, 1, x_1518);
return x_1519;
}
}
block_1472:
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
lean_inc(x_1428);
x_1458 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1426, x_1456, x_1413, x_1428);
x_1459 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_1458, x_3, x_4, x_5, x_6, x_1457);
x_1460 = lean_ctor_get(x_1459, 1);
lean_inc(x_1460);
lean_dec(x_1459);
x_1461 = lean_box(0);
x_1462 = l_Lean_mkConst(x_1428, x_1461);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1462);
x_1463 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1462, x_3, x_4, x_5, x_6, x_1460);
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1463, 1);
lean_inc(x_1465);
lean_dec(x_1463);
x_1466 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed), 11, 4);
lean_closure_set(x_1466, 0, x_1);
lean_closure_set(x_1466, 1, x_1433);
lean_closure_set(x_1466, 2, x_1420);
lean_closure_set(x_1466, 3, x_1462);
x_1467 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1464, x_1466, x_3, x_4, x_5, x_6, x_1465);
return x_1467;
}
else
{
uint8_t x_1468; 
lean_dec(x_1462);
lean_dec(x_1420);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1468 = !lean_is_exclusive(x_1463);
if (x_1468 == 0)
{
return x_1463;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
x_1469 = lean_ctor_get(x_1463, 0);
x_1470 = lean_ctor_get(x_1463, 1);
lean_inc(x_1470);
lean_inc(x_1469);
lean_dec(x_1463);
x_1471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1471, 0, x_1469);
lean_ctor_set(x_1471, 1, x_1470);
return x_1471;
}
}
}
}
else
{
uint8_t x_1520; 
lean_dec(x_1432);
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1420);
lean_dec(x_1413);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1520 = !lean_is_exclusive(x_1453);
if (x_1520 == 0)
{
return x_1453;
}
else
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
x_1521 = lean_ctor_get(x_1453, 0);
x_1522 = lean_ctor_get(x_1453, 1);
lean_inc(x_1522);
lean_inc(x_1521);
lean_dec(x_1453);
x_1523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1523, 0, x_1521);
lean_ctor_set(x_1523, 1, x_1522);
return x_1523;
}
}
}
}
}
else
{
uint8_t x_1553; 
lean_dec(x_1432);
lean_dec(x_1430);
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1425);
lean_dec(x_1420);
lean_dec(x_1413);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1553 = !lean_is_exclusive(x_1434);
if (x_1553 == 0)
{
return x_1434;
}
else
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; 
x_1554 = lean_ctor_get(x_1434, 0);
x_1555 = lean_ctor_get(x_1434, 1);
lean_inc(x_1555);
lean_inc(x_1554);
lean_dec(x_1434);
x_1556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1556, 0, x_1554);
lean_ctor_set(x_1556, 1, x_1555);
return x_1556;
}
}
}
else
{
uint8_t x_1557; 
lean_dec(x_1428);
lean_dec(x_1426);
lean_dec(x_1425);
lean_dec(x_1420);
lean_dec(x_1413);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1557 = !lean_is_exclusive(x_1429);
if (x_1557 == 0)
{
return x_1429;
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1558 = lean_ctor_get(x_1429, 0);
x_1559 = lean_ctor_get(x_1429, 1);
lean_inc(x_1559);
lean_inc(x_1558);
lean_dec(x_1429);
x_1560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1560, 0, x_1558);
lean_ctor_set(x_1560, 1, x_1559);
return x_1560;
}
}
}
else
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; 
lean_dec(x_1426);
lean_dec(x_1425);
lean_dec(x_1413);
lean_dec(x_9);
x_1561 = lean_ctor_get(x_1427, 0);
lean_inc(x_1561);
lean_dec(x_1427);
x_1562 = lean_box(0);
x_1563 = l_Lean_mkConst(x_1561, x_1562);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1563);
x_1564 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1563, x_3, x_4, x_5, x_6, x_1423);
if (lean_obj_tag(x_1564) == 0)
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; 
x_1565 = lean_ctor_get(x_1564, 0);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1564, 1);
lean_inc(x_1566);
lean_dec(x_1564);
x_1567 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed), 10, 3);
lean_closure_set(x_1567, 0, x_1);
lean_closure_set(x_1567, 1, x_1420);
lean_closure_set(x_1567, 2, x_1563);
x_1568 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1565, x_1567, x_3, x_4, x_5, x_6, x_1566);
return x_1568;
}
else
{
uint8_t x_1569; 
lean_dec(x_1563);
lean_dec(x_1420);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1569 = !lean_is_exclusive(x_1564);
if (x_1569 == 0)
{
return x_1564;
}
else
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
x_1570 = lean_ctor_get(x_1564, 0);
x_1571 = lean_ctor_get(x_1564, 1);
lean_inc(x_1571);
lean_inc(x_1570);
lean_dec(x_1564);
x_1572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1572, 0, x_1570);
lean_ctor_set(x_1572, 1, x_1571);
return x_1572;
}
}
}
}
else
{
lean_object* x_1573; 
lean_dec(x_1402);
lean_dec(x_1);
x_1573 = lean_box(0);
x_1403 = x_1573;
goto block_1412;
}
block_1412:
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
lean_dec(x_1403);
x_1404 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1405 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1405, 0, x_1404);
x_1406 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1406, 0, x_1405);
x_1407 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1408 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1408, 0, x_1407);
lean_ctor_set(x_1408, 1, x_1406);
x_1409 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1410 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1410, 0, x_1408);
lean_ctor_set(x_1410, 1, x_1409);
x_1411 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1410, x_3, x_4, x_5, x_6, x_1401);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1411;
}
}
case 11:
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1574 = lean_ctor_get(x_8, 1);
lean_inc(x_1574);
lean_dec(x_8);
x_1575 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1575) == 4)
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1586 = lean_ctor_get(x_1575, 0);
lean_inc(x_1586);
lean_dec(x_1575);
x_1587 = lean_unsigned_to_nat(0u);
x_1588 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1587);
x_1589 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1588);
x_1590 = lean_mk_array(x_1588, x_1589);
x_1591 = lean_unsigned_to_nat(1u);
x_1592 = lean_nat_sub(x_1588, x_1591);
lean_dec(x_1588);
lean_inc(x_9);
x_1593 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1590, x_1592);
x_1594 = lean_st_ref_get(x_6, x_1574);
x_1595 = lean_ctor_get(x_1594, 0);
lean_inc(x_1595);
x_1596 = lean_ctor_get(x_1594, 1);
lean_inc(x_1596);
lean_dec(x_1594);
x_1597 = lean_ctor_get(x_1595, 0);
lean_inc(x_1597);
lean_dec(x_1595);
x_1598 = lean_ctor_get(x_1, 0);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1, 2);
lean_inc(x_1599);
x_1600 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1599, x_1597, x_1586);
lean_dec(x_1597);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1601; lean_object* x_1602; 
lean_inc(x_1598);
x_1601 = l_Lean_Name_append___main(x_1586, x_1598);
lean_inc(x_1586);
x_1602 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1586, x_3, x_4, x_5, x_6, x_1596);
if (lean_obj_tag(x_1602) == 0)
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
x_1603 = lean_ctor_get(x_1602, 0);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1602, 1);
lean_inc(x_1604);
lean_dec(x_1602);
x_1605 = l_Lean_ConstantInfo_type(x_1603);
x_1606 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1605);
x_1607 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1605, x_1606, x_3, x_4, x_5, x_6, x_1604);
if (lean_obj_tag(x_1607) == 0)
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1698; uint8_t x_1699; 
x_1608 = lean_ctor_get(x_1607, 0);
lean_inc(x_1608);
x_1609 = lean_ctor_get(x_1607, 1);
lean_inc(x_1609);
lean_dec(x_1607);
x_1698 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1699 = l_Lean_Expr_isConstOf(x_1608, x_1698);
if (x_1699 == 0)
{
lean_object* x_1700; uint8_t x_1701; 
x_1700 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1701 = l_Lean_Expr_isConstOf(x_1608, x_1700);
lean_dec(x_1608);
if (x_1701 == 0)
{
lean_object* x_1702; 
lean_dec(x_1605);
lean_dec(x_1603);
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1593);
lean_dec(x_1586);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1702 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_1609);
if (lean_obj_tag(x_1702) == 0)
{
lean_object* x_1703; 
x_1703 = lean_ctor_get(x_1702, 0);
lean_inc(x_1703);
if (lean_obj_tag(x_1703) == 0)
{
lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; 
lean_dec(x_1);
x_1704 = lean_ctor_get(x_1702, 1);
lean_inc(x_1704);
lean_dec(x_1702);
x_1705 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1705, 0, x_1598);
x_1706 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1707 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1707, 0, x_1706);
lean_ctor_set(x_1707, 1, x_1705);
x_1708 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1709 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1709, 0, x_1707);
lean_ctor_set(x_1709, 1, x_1708);
x_1710 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1711 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1711, 0, x_1710);
x_1712 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1712, 0, x_1711);
x_1713 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1713, 0, x_1709);
lean_ctor_set(x_1713, 1, x_1712);
x_1714 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1715 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1715, 0, x_1713);
lean_ctor_set(x_1715, 1, x_1714);
x_1716 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1715, x_3, x_4, x_5, x_6, x_1704);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1716;
}
else
{
lean_object* x_1717; lean_object* x_1718; 
lean_dec(x_1598);
lean_dec(x_9);
x_1717 = lean_ctor_get(x_1702, 1);
lean_inc(x_1717);
lean_dec(x_1702);
x_1718 = lean_ctor_get(x_1703, 0);
lean_inc(x_1718);
lean_dec(x_1703);
x_2 = x_1718;
x_7 = x_1717;
goto _start;
}
}
else
{
uint8_t x_1720; 
lean_dec(x_1598);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1720 = !lean_is_exclusive(x_1702);
if (x_1720 == 0)
{
return x_1702;
}
else
{
lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; 
x_1721 = lean_ctor_get(x_1702, 0);
x_1722 = lean_ctor_get(x_1702, 1);
lean_inc(x_1722);
lean_inc(x_1721);
lean_dec(x_1702);
x_1723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1723, 0, x_1721);
lean_ctor_set(x_1723, 1, x_1722);
return x_1723;
}
}
}
else
{
lean_object* x_1724; 
x_1724 = lean_box(0);
x_1610 = x_1724;
goto block_1697;
}
}
else
{
lean_object* x_1725; 
lean_dec(x_1608);
x_1725 = lean_box(0);
x_1610 = x_1725;
goto block_1697;
}
block_1697:
{
lean_object* x_1611; 
lean_dec(x_1610);
x_1611 = l_Lean_ConstantInfo_value_x3f(x_1603);
lean_dec(x_1603);
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; 
lean_dec(x_1605);
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1593);
lean_dec(x_1586);
lean_dec(x_1);
x_1612 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1612, 0, x_1598);
x_1613 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1614 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1614, 0, x_1613);
lean_ctor_set(x_1614, 1, x_1612);
x_1615 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1616 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1616, 0, x_1614);
lean_ctor_set(x_1616, 1, x_1615);
x_1617 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1618 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1618, 0, x_1617);
x_1619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1619, 0, x_1618);
x_1620 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1620, 0, x_1616);
lean_ctor_set(x_1620, 1, x_1619);
x_1621 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1622 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1622, 0, x_1620);
lean_ctor_set(x_1622, 1, x_1621);
x_1623 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1622, x_3, x_4, x_5, x_6, x_1609);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1623;
}
else
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; 
lean_dec(x_1598);
lean_dec(x_9);
x_1624 = lean_ctor_get(x_1611, 0);
lean_inc(x_1624);
lean_dec(x_1611);
x_1625 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1624);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1626 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1625, x_3, x_4, x_5, x_6, x_1609);
if (lean_obj_tag(x_1626) == 0)
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
x_1627 = lean_ctor_get(x_1626, 0);
lean_inc(x_1627);
x_1628 = lean_ctor_get(x_1626, 1);
lean_inc(x_1628);
lean_dec(x_1626);
x_1646 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1647 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed), 9, 2);
lean_closure_set(x_1647, 0, x_1);
lean_closure_set(x_1647, 1, x_1646);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1648 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1605, x_1647, x_3, x_4, x_5, x_6, x_1628);
if (lean_obj_tag(x_1648) == 0)
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; uint8_t x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; 
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1648, 1);
lean_inc(x_1650);
lean_dec(x_1648);
x_1651 = lean_box(0);
lean_inc(x_1601);
x_1652 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1652, 0, x_1601);
lean_ctor_set(x_1652, 1, x_1651);
lean_ctor_set(x_1652, 2, x_1649);
x_1653 = lean_box(0);
x_1654 = 0;
x_1655 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1655, 0, x_1652);
lean_ctor_set(x_1655, 1, x_1627);
lean_ctor_set(x_1655, 2, x_1653);
lean_ctor_set_uint8(x_1655, sizeof(void*)*3, x_1654);
x_1656 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1656, 0, x_1655);
x_1657 = lean_st_ref_get(x_6, x_1650);
x_1658 = lean_ctor_get(x_1657, 0);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1657, 1);
lean_inc(x_1659);
lean_dec(x_1657);
x_1660 = lean_ctor_get(x_1658, 0);
lean_inc(x_1660);
lean_dec(x_1658);
x_1661 = l_Lean_Environment_addAndCompile(x_1660, x_1651, x_1656);
lean_dec(x_1656);
if (lean_obj_tag(x_1661) == 0)
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; 
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1593);
lean_dec(x_1586);
lean_dec(x_1);
x_1662 = lean_ctor_get(x_1661, 0);
lean_inc(x_1662);
lean_dec(x_1661);
x_1663 = l_Lean_KernelException_toMessageData(x_1662, x_1651);
x_1664 = lean_ctor_get(x_5, 3);
lean_inc(x_1664);
x_1665 = l_Lean_MessageData_toString(x_1663, x_1659);
if (lean_obj_tag(x_1665) == 0)
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; uint8_t x_1671; 
lean_dec(x_1664);
x_1666 = lean_ctor_get(x_1665, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1665, 1);
lean_inc(x_1667);
lean_dec(x_1665);
x_1668 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1668, 0, x_1666);
x_1669 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1669, 0, x_1668);
x_1670 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1669, x_3, x_4, x_5, x_6, x_1667);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1671 = !lean_is_exclusive(x_1670);
if (x_1671 == 0)
{
return x_1670;
}
else
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; 
x_1672 = lean_ctor_get(x_1670, 0);
x_1673 = lean_ctor_get(x_1670, 1);
lean_inc(x_1673);
lean_inc(x_1672);
lean_dec(x_1670);
x_1674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1674, 0, x_1672);
lean_ctor_set(x_1674, 1, x_1673);
return x_1674;
}
}
else
{
uint8_t x_1675; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1675 = !lean_is_exclusive(x_1665);
if (x_1675 == 0)
{
lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; 
x_1676 = lean_ctor_get(x_1665, 0);
x_1677 = lean_io_error_to_string(x_1676);
x_1678 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1678, 0, x_1677);
x_1679 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1679, 0, x_1678);
x_1680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1680, 0, x_1664);
lean_ctor_set(x_1680, 1, x_1679);
lean_ctor_set(x_1665, 0, x_1680);
return x_1665;
}
else
{
lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; 
x_1681 = lean_ctor_get(x_1665, 0);
x_1682 = lean_ctor_get(x_1665, 1);
lean_inc(x_1682);
lean_inc(x_1681);
lean_dec(x_1665);
x_1683 = lean_io_error_to_string(x_1681);
x_1684 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1684, 0, x_1683);
x_1685 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1685, 0, x_1684);
x_1686 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1686, 0, x_1664);
lean_ctor_set(x_1686, 1, x_1685);
x_1687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1687, 0, x_1686);
lean_ctor_set(x_1687, 1, x_1682);
return x_1687;
}
}
}
else
{
lean_object* x_1688; 
x_1688 = lean_ctor_get(x_1661, 0);
lean_inc(x_1688);
lean_dec(x_1661);
x_1629 = x_1688;
x_1630 = x_1659;
goto block_1645;
}
}
else
{
uint8_t x_1689; 
lean_dec(x_1627);
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1593);
lean_dec(x_1586);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1689 = !lean_is_exclusive(x_1648);
if (x_1689 == 0)
{
return x_1648;
}
else
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; 
x_1690 = lean_ctor_get(x_1648, 0);
x_1691 = lean_ctor_get(x_1648, 1);
lean_inc(x_1691);
lean_inc(x_1690);
lean_dec(x_1648);
x_1692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1692, 0, x_1690);
lean_ctor_set(x_1692, 1, x_1691);
return x_1692;
}
}
block_1645:
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
lean_inc(x_1601);
x_1631 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1599, x_1629, x_1586, x_1601);
x_1632 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_1631, x_3, x_4, x_5, x_6, x_1630);
x_1633 = lean_ctor_get(x_1632, 1);
lean_inc(x_1633);
lean_dec(x_1632);
x_1634 = lean_box(0);
x_1635 = l_Lean_mkConst(x_1601, x_1634);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1635);
x_1636 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1635, x_3, x_4, x_5, x_6, x_1633);
if (lean_obj_tag(x_1636) == 0)
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; 
x_1637 = lean_ctor_get(x_1636, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1636, 1);
lean_inc(x_1638);
lean_dec(x_1636);
x_1639 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed), 11, 4);
lean_closure_set(x_1639, 0, x_1);
lean_closure_set(x_1639, 1, x_1606);
lean_closure_set(x_1639, 2, x_1593);
lean_closure_set(x_1639, 3, x_1635);
x_1640 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1637, x_1639, x_3, x_4, x_5, x_6, x_1638);
return x_1640;
}
else
{
uint8_t x_1641; 
lean_dec(x_1635);
lean_dec(x_1593);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1641 = !lean_is_exclusive(x_1636);
if (x_1641 == 0)
{
return x_1636;
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1642 = lean_ctor_get(x_1636, 0);
x_1643 = lean_ctor_get(x_1636, 1);
lean_inc(x_1643);
lean_inc(x_1642);
lean_dec(x_1636);
x_1644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1644, 0, x_1642);
lean_ctor_set(x_1644, 1, x_1643);
return x_1644;
}
}
}
}
else
{
uint8_t x_1693; 
lean_dec(x_1605);
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1593);
lean_dec(x_1586);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1693 = !lean_is_exclusive(x_1626);
if (x_1693 == 0)
{
return x_1626;
}
else
{
lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; 
x_1694 = lean_ctor_get(x_1626, 0);
x_1695 = lean_ctor_get(x_1626, 1);
lean_inc(x_1695);
lean_inc(x_1694);
lean_dec(x_1626);
x_1696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1696, 0, x_1694);
lean_ctor_set(x_1696, 1, x_1695);
return x_1696;
}
}
}
}
}
else
{
uint8_t x_1726; 
lean_dec(x_1605);
lean_dec(x_1603);
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1598);
lean_dec(x_1593);
lean_dec(x_1586);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1726 = !lean_is_exclusive(x_1607);
if (x_1726 == 0)
{
return x_1607;
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
x_1727 = lean_ctor_get(x_1607, 0);
x_1728 = lean_ctor_get(x_1607, 1);
lean_inc(x_1728);
lean_inc(x_1727);
lean_dec(x_1607);
x_1729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1729, 0, x_1727);
lean_ctor_set(x_1729, 1, x_1728);
return x_1729;
}
}
}
else
{
uint8_t x_1730; 
lean_dec(x_1601);
lean_dec(x_1599);
lean_dec(x_1598);
lean_dec(x_1593);
lean_dec(x_1586);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1730 = !lean_is_exclusive(x_1602);
if (x_1730 == 0)
{
return x_1602;
}
else
{
lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; 
x_1731 = lean_ctor_get(x_1602, 0);
x_1732 = lean_ctor_get(x_1602, 1);
lean_inc(x_1732);
lean_inc(x_1731);
lean_dec(x_1602);
x_1733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1733, 0, x_1731);
lean_ctor_set(x_1733, 1, x_1732);
return x_1733;
}
}
}
else
{
lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; 
lean_dec(x_1599);
lean_dec(x_1598);
lean_dec(x_1586);
lean_dec(x_9);
x_1734 = lean_ctor_get(x_1600, 0);
lean_inc(x_1734);
lean_dec(x_1600);
x_1735 = lean_box(0);
x_1736 = l_Lean_mkConst(x_1734, x_1735);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1736);
x_1737 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1736, x_3, x_4, x_5, x_6, x_1596);
if (lean_obj_tag(x_1737) == 0)
{
lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; 
x_1738 = lean_ctor_get(x_1737, 0);
lean_inc(x_1738);
x_1739 = lean_ctor_get(x_1737, 1);
lean_inc(x_1739);
lean_dec(x_1737);
x_1740 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed), 10, 3);
lean_closure_set(x_1740, 0, x_1);
lean_closure_set(x_1740, 1, x_1593);
lean_closure_set(x_1740, 2, x_1736);
x_1741 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1738, x_1740, x_3, x_4, x_5, x_6, x_1739);
return x_1741;
}
else
{
uint8_t x_1742; 
lean_dec(x_1736);
lean_dec(x_1593);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1742 = !lean_is_exclusive(x_1737);
if (x_1742 == 0)
{
return x_1737;
}
else
{
lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; 
x_1743 = lean_ctor_get(x_1737, 0);
x_1744 = lean_ctor_get(x_1737, 1);
lean_inc(x_1744);
lean_inc(x_1743);
lean_dec(x_1737);
x_1745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1745, 0, x_1743);
lean_ctor_set(x_1745, 1, x_1744);
return x_1745;
}
}
}
}
else
{
lean_object* x_1746; 
lean_dec(x_1575);
lean_dec(x_1);
x_1746 = lean_box(0);
x_1576 = x_1746;
goto block_1585;
}
block_1585:
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; 
lean_dec(x_1576);
x_1577 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1578 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1578, 0, x_1577);
x_1579 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1579, 0, x_1578);
x_1580 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1581 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1581, 0, x_1580);
lean_ctor_set(x_1581, 1, x_1579);
x_1582 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1583 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1583, 0, x_1581);
lean_ctor_set(x_1583, 1, x_1582);
x_1584 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1583, x_3, x_4, x_5, x_6, x_1574);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1584;
}
}
default: 
{
lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; 
x_1747 = lean_ctor_get(x_8, 1);
lean_inc(x_1747);
lean_dec(x_8);
x_1748 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1748) == 4)
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; 
x_1759 = lean_ctor_get(x_1748, 0);
lean_inc(x_1759);
lean_dec(x_1748);
x_1760 = lean_unsigned_to_nat(0u);
x_1761 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1760);
x_1762 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1761);
x_1763 = lean_mk_array(x_1761, x_1762);
x_1764 = lean_unsigned_to_nat(1u);
x_1765 = lean_nat_sub(x_1761, x_1764);
lean_dec(x_1761);
lean_inc(x_9);
x_1766 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1763, x_1765);
x_1767 = lean_st_ref_get(x_6, x_1747);
x_1768 = lean_ctor_get(x_1767, 0);
lean_inc(x_1768);
x_1769 = lean_ctor_get(x_1767, 1);
lean_inc(x_1769);
lean_dec(x_1767);
x_1770 = lean_ctor_get(x_1768, 0);
lean_inc(x_1770);
lean_dec(x_1768);
x_1771 = lean_ctor_get(x_1, 0);
lean_inc(x_1771);
x_1772 = lean_ctor_get(x_1, 2);
lean_inc(x_1772);
x_1773 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1772, x_1770, x_1759);
lean_dec(x_1770);
if (lean_obj_tag(x_1773) == 0)
{
lean_object* x_1774; lean_object* x_1775; 
lean_inc(x_1771);
x_1774 = l_Lean_Name_append___main(x_1759, x_1771);
lean_inc(x_1759);
x_1775 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1759, x_3, x_4, x_5, x_6, x_1769);
if (lean_obj_tag(x_1775) == 0)
{
lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; 
x_1776 = lean_ctor_get(x_1775, 0);
lean_inc(x_1776);
x_1777 = lean_ctor_get(x_1775, 1);
lean_inc(x_1777);
lean_dec(x_1775);
x_1778 = l_Lean_ConstantInfo_type(x_1776);
x_1779 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1778);
x_1780 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1778, x_1779, x_3, x_4, x_5, x_6, x_1777);
if (lean_obj_tag(x_1780) == 0)
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1871; uint8_t x_1872; 
x_1781 = lean_ctor_get(x_1780, 0);
lean_inc(x_1781);
x_1782 = lean_ctor_get(x_1780, 1);
lean_inc(x_1782);
lean_dec(x_1780);
x_1871 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1872 = l_Lean_Expr_isConstOf(x_1781, x_1871);
if (x_1872 == 0)
{
lean_object* x_1873; uint8_t x_1874; 
x_1873 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1874 = l_Lean_Expr_isConstOf(x_1781, x_1873);
lean_dec(x_1781);
if (x_1874 == 0)
{
lean_object* x_1875; 
lean_dec(x_1778);
lean_dec(x_1776);
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1766);
lean_dec(x_1759);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1875 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_1782);
if (lean_obj_tag(x_1875) == 0)
{
lean_object* x_1876; 
x_1876 = lean_ctor_get(x_1875, 0);
lean_inc(x_1876);
if (lean_obj_tag(x_1876) == 0)
{
lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; 
lean_dec(x_1);
x_1877 = lean_ctor_get(x_1875, 1);
lean_inc(x_1877);
lean_dec(x_1875);
x_1878 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1878, 0, x_1771);
x_1879 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1880 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1880, 0, x_1879);
lean_ctor_set(x_1880, 1, x_1878);
x_1881 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1882 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1882, 0, x_1880);
lean_ctor_set(x_1882, 1, x_1881);
x_1883 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1884 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1884, 0, x_1883);
x_1885 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1885, 0, x_1884);
x_1886 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1886, 0, x_1882);
lean_ctor_set(x_1886, 1, x_1885);
x_1887 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1888 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1888, 0, x_1886);
lean_ctor_set(x_1888, 1, x_1887);
x_1889 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1888, x_3, x_4, x_5, x_6, x_1877);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1889;
}
else
{
lean_object* x_1890; lean_object* x_1891; 
lean_dec(x_1771);
lean_dec(x_9);
x_1890 = lean_ctor_get(x_1875, 1);
lean_inc(x_1890);
lean_dec(x_1875);
x_1891 = lean_ctor_get(x_1876, 0);
lean_inc(x_1891);
lean_dec(x_1876);
x_2 = x_1891;
x_7 = x_1890;
goto _start;
}
}
else
{
uint8_t x_1893; 
lean_dec(x_1771);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1893 = !lean_is_exclusive(x_1875);
if (x_1893 == 0)
{
return x_1875;
}
else
{
lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; 
x_1894 = lean_ctor_get(x_1875, 0);
x_1895 = lean_ctor_get(x_1875, 1);
lean_inc(x_1895);
lean_inc(x_1894);
lean_dec(x_1875);
x_1896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1896, 0, x_1894);
lean_ctor_set(x_1896, 1, x_1895);
return x_1896;
}
}
}
else
{
lean_object* x_1897; 
x_1897 = lean_box(0);
x_1783 = x_1897;
goto block_1870;
}
}
else
{
lean_object* x_1898; 
lean_dec(x_1781);
x_1898 = lean_box(0);
x_1783 = x_1898;
goto block_1870;
}
block_1870:
{
lean_object* x_1784; 
lean_dec(x_1783);
x_1784 = l_Lean_ConstantInfo_value_x3f(x_1776);
lean_dec(x_1776);
if (lean_obj_tag(x_1784) == 0)
{
lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; 
lean_dec(x_1778);
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1766);
lean_dec(x_1759);
lean_dec(x_1);
x_1785 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1785, 0, x_1771);
x_1786 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1787 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1787, 0, x_1786);
lean_ctor_set(x_1787, 1, x_1785);
x_1788 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1789 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1789, 0, x_1787);
lean_ctor_set(x_1789, 1, x_1788);
x_1790 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1791 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1791, 0, x_1790);
x_1792 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1792, 0, x_1791);
x_1793 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1793, 0, x_1789);
lean_ctor_set(x_1793, 1, x_1792);
x_1794 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1795 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1795, 0, x_1793);
lean_ctor_set(x_1795, 1, x_1794);
x_1796 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1795, x_3, x_4, x_5, x_6, x_1782);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1796;
}
else
{
lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; 
lean_dec(x_1771);
lean_dec(x_9);
x_1797 = lean_ctor_get(x_1784, 0);
lean_inc(x_1797);
lean_dec(x_1784);
x_1798 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1797);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1799 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1798, x_3, x_4, x_5, x_6, x_1782);
if (lean_obj_tag(x_1799) == 0)
{
lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; 
x_1800 = lean_ctor_get(x_1799, 0);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1799, 1);
lean_inc(x_1801);
lean_dec(x_1799);
x_1819 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1820 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed), 9, 2);
lean_closure_set(x_1820, 0, x_1);
lean_closure_set(x_1820, 1, x_1819);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1821 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1778, x_1820, x_3, x_4, x_5, x_6, x_1801);
if (lean_obj_tag(x_1821) == 0)
{
lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; uint8_t x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; 
x_1822 = lean_ctor_get(x_1821, 0);
lean_inc(x_1822);
x_1823 = lean_ctor_get(x_1821, 1);
lean_inc(x_1823);
lean_dec(x_1821);
x_1824 = lean_box(0);
lean_inc(x_1774);
x_1825 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1825, 0, x_1774);
lean_ctor_set(x_1825, 1, x_1824);
lean_ctor_set(x_1825, 2, x_1822);
x_1826 = lean_box(0);
x_1827 = 0;
x_1828 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1828, 0, x_1825);
lean_ctor_set(x_1828, 1, x_1800);
lean_ctor_set(x_1828, 2, x_1826);
lean_ctor_set_uint8(x_1828, sizeof(void*)*3, x_1827);
x_1829 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1829, 0, x_1828);
x_1830 = lean_st_ref_get(x_6, x_1823);
x_1831 = lean_ctor_get(x_1830, 0);
lean_inc(x_1831);
x_1832 = lean_ctor_get(x_1830, 1);
lean_inc(x_1832);
lean_dec(x_1830);
x_1833 = lean_ctor_get(x_1831, 0);
lean_inc(x_1833);
lean_dec(x_1831);
x_1834 = l_Lean_Environment_addAndCompile(x_1833, x_1824, x_1829);
lean_dec(x_1829);
if (lean_obj_tag(x_1834) == 0)
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; 
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1766);
lean_dec(x_1759);
lean_dec(x_1);
x_1835 = lean_ctor_get(x_1834, 0);
lean_inc(x_1835);
lean_dec(x_1834);
x_1836 = l_Lean_KernelException_toMessageData(x_1835, x_1824);
x_1837 = lean_ctor_get(x_5, 3);
lean_inc(x_1837);
x_1838 = l_Lean_MessageData_toString(x_1836, x_1832);
if (lean_obj_tag(x_1838) == 0)
{
lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; uint8_t x_1844; 
lean_dec(x_1837);
x_1839 = lean_ctor_get(x_1838, 0);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1838, 1);
lean_inc(x_1840);
lean_dec(x_1838);
x_1841 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1841, 0, x_1839);
x_1842 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1842, 0, x_1841);
x_1843 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1842, x_3, x_4, x_5, x_6, x_1840);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1844 = !lean_is_exclusive(x_1843);
if (x_1844 == 0)
{
return x_1843;
}
else
{
lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; 
x_1845 = lean_ctor_get(x_1843, 0);
x_1846 = lean_ctor_get(x_1843, 1);
lean_inc(x_1846);
lean_inc(x_1845);
lean_dec(x_1843);
x_1847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1847, 0, x_1845);
lean_ctor_set(x_1847, 1, x_1846);
return x_1847;
}
}
else
{
uint8_t x_1848; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1848 = !lean_is_exclusive(x_1838);
if (x_1848 == 0)
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; 
x_1849 = lean_ctor_get(x_1838, 0);
x_1850 = lean_io_error_to_string(x_1849);
x_1851 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1851, 0, x_1850);
x_1852 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1852, 0, x_1851);
x_1853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1853, 0, x_1837);
lean_ctor_set(x_1853, 1, x_1852);
lean_ctor_set(x_1838, 0, x_1853);
return x_1838;
}
else
{
lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; 
x_1854 = lean_ctor_get(x_1838, 0);
x_1855 = lean_ctor_get(x_1838, 1);
lean_inc(x_1855);
lean_inc(x_1854);
lean_dec(x_1838);
x_1856 = lean_io_error_to_string(x_1854);
x_1857 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1857, 0, x_1856);
x_1858 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1858, 0, x_1857);
x_1859 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1859, 0, x_1837);
lean_ctor_set(x_1859, 1, x_1858);
x_1860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1860, 0, x_1859);
lean_ctor_set(x_1860, 1, x_1855);
return x_1860;
}
}
}
else
{
lean_object* x_1861; 
x_1861 = lean_ctor_get(x_1834, 0);
lean_inc(x_1861);
lean_dec(x_1834);
x_1802 = x_1861;
x_1803 = x_1832;
goto block_1818;
}
}
else
{
uint8_t x_1862; 
lean_dec(x_1800);
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1766);
lean_dec(x_1759);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1862 = !lean_is_exclusive(x_1821);
if (x_1862 == 0)
{
return x_1821;
}
else
{
lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; 
x_1863 = lean_ctor_get(x_1821, 0);
x_1864 = lean_ctor_get(x_1821, 1);
lean_inc(x_1864);
lean_inc(x_1863);
lean_dec(x_1821);
x_1865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1865, 0, x_1863);
lean_ctor_set(x_1865, 1, x_1864);
return x_1865;
}
}
block_1818:
{
lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; 
lean_inc(x_1774);
x_1804 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1772, x_1802, x_1759, x_1774);
x_1805 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_1804, x_3, x_4, x_5, x_6, x_1803);
x_1806 = lean_ctor_get(x_1805, 1);
lean_inc(x_1806);
lean_dec(x_1805);
x_1807 = lean_box(0);
x_1808 = l_Lean_mkConst(x_1774, x_1807);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1808);
x_1809 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1808, x_3, x_4, x_5, x_6, x_1806);
if (lean_obj_tag(x_1809) == 0)
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; 
x_1810 = lean_ctor_get(x_1809, 0);
lean_inc(x_1810);
x_1811 = lean_ctor_get(x_1809, 1);
lean_inc(x_1811);
lean_dec(x_1809);
x_1812 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed), 11, 4);
lean_closure_set(x_1812, 0, x_1);
lean_closure_set(x_1812, 1, x_1779);
lean_closure_set(x_1812, 2, x_1766);
lean_closure_set(x_1812, 3, x_1808);
x_1813 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1810, x_1812, x_3, x_4, x_5, x_6, x_1811);
return x_1813;
}
else
{
uint8_t x_1814; 
lean_dec(x_1808);
lean_dec(x_1766);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1814 = !lean_is_exclusive(x_1809);
if (x_1814 == 0)
{
return x_1809;
}
else
{
lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; 
x_1815 = lean_ctor_get(x_1809, 0);
x_1816 = lean_ctor_get(x_1809, 1);
lean_inc(x_1816);
lean_inc(x_1815);
lean_dec(x_1809);
x_1817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1817, 0, x_1815);
lean_ctor_set(x_1817, 1, x_1816);
return x_1817;
}
}
}
}
else
{
uint8_t x_1866; 
lean_dec(x_1778);
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1766);
lean_dec(x_1759);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1866 = !lean_is_exclusive(x_1799);
if (x_1866 == 0)
{
return x_1799;
}
else
{
lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; 
x_1867 = lean_ctor_get(x_1799, 0);
x_1868 = lean_ctor_get(x_1799, 1);
lean_inc(x_1868);
lean_inc(x_1867);
lean_dec(x_1799);
x_1869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1869, 0, x_1867);
lean_ctor_set(x_1869, 1, x_1868);
return x_1869;
}
}
}
}
}
else
{
uint8_t x_1899; 
lean_dec(x_1778);
lean_dec(x_1776);
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1771);
lean_dec(x_1766);
lean_dec(x_1759);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1899 = !lean_is_exclusive(x_1780);
if (x_1899 == 0)
{
return x_1780;
}
else
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; 
x_1900 = lean_ctor_get(x_1780, 0);
x_1901 = lean_ctor_get(x_1780, 1);
lean_inc(x_1901);
lean_inc(x_1900);
lean_dec(x_1780);
x_1902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1902, 0, x_1900);
lean_ctor_set(x_1902, 1, x_1901);
return x_1902;
}
}
}
else
{
uint8_t x_1903; 
lean_dec(x_1774);
lean_dec(x_1772);
lean_dec(x_1771);
lean_dec(x_1766);
lean_dec(x_1759);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1903 = !lean_is_exclusive(x_1775);
if (x_1903 == 0)
{
return x_1775;
}
else
{
lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; 
x_1904 = lean_ctor_get(x_1775, 0);
x_1905 = lean_ctor_get(x_1775, 1);
lean_inc(x_1905);
lean_inc(x_1904);
lean_dec(x_1775);
x_1906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1906, 0, x_1904);
lean_ctor_set(x_1906, 1, x_1905);
return x_1906;
}
}
}
else
{
lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; 
lean_dec(x_1772);
lean_dec(x_1771);
lean_dec(x_1759);
lean_dec(x_9);
x_1907 = lean_ctor_get(x_1773, 0);
lean_inc(x_1907);
lean_dec(x_1773);
x_1908 = lean_box(0);
x_1909 = l_Lean_mkConst(x_1907, x_1908);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1909);
x_1910 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1909, x_3, x_4, x_5, x_6, x_1769);
if (lean_obj_tag(x_1910) == 0)
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
x_1911 = lean_ctor_get(x_1910, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1910, 1);
lean_inc(x_1912);
lean_dec(x_1910);
x_1913 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed), 10, 3);
lean_closure_set(x_1913, 0, x_1);
lean_closure_set(x_1913, 1, x_1766);
lean_closure_set(x_1913, 2, x_1909);
x_1914 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1911, x_1913, x_3, x_4, x_5, x_6, x_1912);
return x_1914;
}
else
{
uint8_t x_1915; 
lean_dec(x_1909);
lean_dec(x_1766);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1915 = !lean_is_exclusive(x_1910);
if (x_1915 == 0)
{
return x_1910;
}
else
{
lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; 
x_1916 = lean_ctor_get(x_1910, 0);
x_1917 = lean_ctor_get(x_1910, 1);
lean_inc(x_1917);
lean_inc(x_1916);
lean_dec(x_1910);
x_1918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1918, 0, x_1916);
lean_ctor_set(x_1918, 1, x_1917);
return x_1918;
}
}
}
}
else
{
lean_object* x_1919; 
lean_dec(x_1748);
lean_dec(x_1);
x_1919 = lean_box(0);
x_1749 = x_1919;
goto block_1758;
}
block_1758:
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; 
lean_dec(x_1749);
x_1750 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1751 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1751, 0, x_1750);
x_1752 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1752, 0, x_1751);
x_1753 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1754 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1754, 0, x_1753);
lean_ctor_set(x_1754, 1, x_1752);
x_1755 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1756 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1756, 0, x_1754);
lean_ctor_set(x_1756, 1, x_1755);
x_1757 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1756, x_3, x_4, x_5, x_6, x_1747);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1757;
}
}
}
}
else
{
uint8_t x_1920; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1920 = !lean_is_exclusive(x_8);
if (x_1920 == 0)
{
return x_8;
}
else
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; 
x_1921 = lean_ctor_get(x_8, 0);
x_1922 = lean_ctor_get(x_8, 1);
lean_inc(x_1922);
lean_inc(x_1921);
lean_dec(x_8);
x_1923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1923, 0, x_1921);
lean_ctor_set(x_1923, 1, x_1922);
return x_1923;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___main___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___main___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__34___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg), 7, 0);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_inhabited___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParser___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = l_Lean_mkConst(x_2, x_8);
x_10 = l_Lean_Meta_State_inhabited___closed__7;
x_11 = lean_st_mk_ref(x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_9, x_14, x_12, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_12, x_17);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_mk_syntax_ident(x_2);
x_22 = l_Lean_mkOptionalNode___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_nullKind;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
if (x_3 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = 1;
x_30 = l_Lean_addAttribute(x_20, x_28, x_25, x_29, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_30) == 0)
{
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = 1;
x_41 = l_Lean_addAttribute(x_20, x_39, x_25, x_40, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_41) == 0)
{
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set_tag(x_41, 0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_dec(x_18);
x_49 = l_Lean_ParserCompiler_compileParser___rarg___closed__2;
x_50 = l_unreachable_x21___rarg(x_49);
x_51 = lean_apply_4(x_50, x_4, x_5, x_6, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
return x_15;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParser___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lean_getConstInfo___at_Lean_mkInitAttr___spec__1(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
x_16 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_19 = l_Lean_Expr_isConstOf(x_15, x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_10);
x_20 = lean_eval_const(x_14, x_2);
lean_dec(x_2);
lean_dec(x_14);
x_21 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_20, x_3, x_4, x_5, x_13);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_apply_5(x_24, x_22, x_3, x_4, x_5, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_30, x_14, x_2);
lean_dec(x_14);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_free_object(x_10);
x_32 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_32, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_5, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lean_Name_append___main(x_2, x_39);
lean_dec(x_2);
x_41 = lean_eval_const(x_38, x_40);
lean_dec(x_40);
lean_dec(x_38);
x_42 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_41, x_3, x_4, x_5, x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
lean_dec(x_31);
lean_ctor_set(x_10, 0, x_47);
return x_10;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_15);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_48, x_14, x_2);
lean_dec(x_14);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; lean_object* x_51; 
lean_free_object(x_10);
x_50 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_50, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_5, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = l_Lean_Name_append___main(x_2, x_57);
lean_dec(x_2);
x_59 = lean_eval_const(x_56, x_58);
lean_dec(x_58);
lean_dec(x_56);
x_60 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_59, x_3, x_4, x_5, x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_59);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
lean_dec(x_49);
lean_ctor_set(x_10, 0, x_65);
return x_10;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_10, 0);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_10);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
x_70 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_71 = l_Lean_Expr_isConstOf(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_73 = l_Lean_Expr_isConstOf(x_69, x_72);
lean_dec(x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_eval_const(x_68, x_2);
lean_dec(x_2);
lean_dec(x_68);
x_75 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_74, x_3, x_4, x_5, x_67);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_1, 3);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_apply_5(x_78, x_76, x_3, x_4, x_5, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
x_85 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_84, x_68, x_2);
lean_dec(x_68);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; lean_object* x_87; 
x_86 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_86, x_3, x_4, x_5, x_67);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_st_ref_get(x_5, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l_Lean_Name_append___main(x_2, x_93);
lean_dec(x_2);
x_95 = lean_eval_const(x_92, x_94);
lean_dec(x_94);
lean_dec(x_92);
x_96 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_95, x_3, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_85, 0);
lean_inc(x_101);
lean_dec(x_85);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_67);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_69);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
x_104 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_103, x_68, x_2);
lean_dec(x_68);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; lean_object* x_106; 
x_105 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_106 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_105, x_3, x_4, x_5, x_67);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_5, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
lean_dec(x_1);
x_113 = l_Lean_Name_append___main(x_2, x_112);
lean_dec(x_2);
x_114 = lean_eval_const(x_111, x_113);
lean_dec(x_113);
lean_dec(x_111);
x_115 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_114, x_3, x_4, x_5, x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_106, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_118 = x_106;
} else {
 lean_dec_ref(x_106);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_104, 0);
lean_inc(x_120);
lean_dec(x_104);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_67);
return x_121;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_7);
if (x_122 == 0)
{
return x_7;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_7, 0);
x_124 = lean_ctor_get(x_7, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_7);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_interpretParser___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_KeyedDeclsAttribute_Table_insert___rarg(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_KeyedDeclsAttribute_Table_insert___rarg(x_8, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_4 == 0)
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_ParserCompiler_interpretParser___rarg(x_1, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1), 3, 2);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_10);
x_19 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_17, x_15, x_18);
lean_dec(x_17);
x_20 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(x_19, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
x_25 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed), 8, 1);
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
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
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
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1);
l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1 = _init_l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1();
lean_mark_persistent(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12);
l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13 = _init_l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13);
l_Lean_ParserCompiler_compileParser___rarg___closed__1 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__1);
l_Lean_ParserCompiler_compileParser___rarg___closed__2 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
