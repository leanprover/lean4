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
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__3;
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__2(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__5;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__6;
lean_object* l_Lean_ParserCompiler_interpretParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_CoreM___instance__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAttribute(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__4;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__8;
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser_match__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_ParserCompiler_compileParserBody___spec__18(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__6(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_Meta_Basic___instance__5___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__2;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__1(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkSimpleThunk___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16(lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_Table_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3(lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser_match__1(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__3(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__12;
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__10;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__5(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody_match__4(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__53___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_Meta_Basic___instance__11___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__4;
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_ParserCompiler_compileParserBody___spec__18___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__56___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_mkAppStx___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_4 = l_Lean_Expr_isConstOf(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_7 = lean_box(0);
x_8 = l_Lean_mkConst(x_6, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = 8192;
x_5 = l_Lean_Expr_ReplaceImpl_initCache;
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_3, x_4, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_preprocessParserBody___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserBody_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserBody_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserBody_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParserBody_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_ParserCompiler_compileParserBody_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody_match__6___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
else
{
uint8_t x_13; 
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
lean_object* l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isConstOf(x_4, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_mkApp(x_1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_HashMap_inhabited___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = 1;
x_21 = 0;
x_22 = l_Lean_MetavarContext_MkBinding_mkBinding(x_20, x_9, x_1, x_2, x_21, x_21, x_19);
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
x_27 = lean_st_ref_take(x_6, x_16);
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
x_35 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_34, x_3, x_4, x_5, x_6, x_33);
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
x_47 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_46, x_3, x_4, x_5, x_6, x_45);
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
x_53 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_52, x_3, x_4, x_5, x_6, x_16);
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
x_63 = l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
x_64 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_63, x_3, x_4, x_5, x_6, x_62);
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
x_71 = l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
x_72 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_71, x_3, x_4, x_5, x_6, x_70);
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
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_ParserCompiler_compileParserBody___spec__18___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_ParserCompiler_compileParserBody___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_Lean_ParserCompiler_compileParserBody___spec__18___rarg), 7, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_mkSimpleThunk___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_20, x_8, x_9, x_10, x_11, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_22;
x_7 = x_32;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_20, x_35, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_7, x_37, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_6 = x_22;
x_7 = x_40;
x_12 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_19, x_7, x_8, x_9, x_10, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_5 = x_21;
x_6 = x_32;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_19, x_35, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_6, x_37, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_21;
x_6 = x_40;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__2___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__1___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__3(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__5(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__7___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__6___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__8(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__8(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__12___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__11___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__13(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__11(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__17___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__16___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__18(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__14(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__22___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__21___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__23(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___spec__17(x_2, x_11, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__19(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__28___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__27___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__29(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__22(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__33___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__32___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__34(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__25(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__38___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__37___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__39(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__28(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__43___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__42___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__44(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__31(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__48___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__47___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__49(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__34(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__53(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg(x_2, x_3, x_5, x_5, x_18, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__54(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_14 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1, x_8, x_2, x_3);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkConst(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__53___boxed), 11, 4);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_7);
lean_closure_set(x_21, 3, x_17);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_2);
x_17 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_16, x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__52___boxed), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_4, x_21, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_st_ref_get(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_addAndCompile(x_33, x_25, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_KernelException_toMessageData(x_35, x_25);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_Lean_MessageData_toString(x_36, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_io_error_to_string(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__54(x_6, x_7, x_5, x_25, x_8, x_1, x_9, x_61, x_11, x_12, x_13, x_14, x_32);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
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
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg(x_2, x_4, x_4, x_17, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("call of unknown parser at '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to generate ");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" for non-definition '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refusing to generate code for imported parser declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'; use `@[runParserAttributeHooks]` on its definition instead.");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" for non-parser combinator '");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_7, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_19, x_17, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_18);
x_21 = l_Lean_Name_append(x_13, x_18);
lean_inc(x_13);
x_22 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_13, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_ConstantInfo_type(x_23);
x_26 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_25);
x_27 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_25, x_26, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_31 = l_Lean_Expr_isConstOf(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_64 = l_Lean_Expr_isConstOf(x_28, x_63);
lean_dec(x_28);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_65 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_68, 0, x_18);
x_69 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_10);
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_76, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_18);
lean_dec(x_10);
x_78 = lean_ctor_get(x_65, 1);
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_ctor_get(x_66, 0);
lean_inc(x_79);
lean_dec(x_66);
x_80 = 0;
x_2 = x_79;
x_3 = x_80;
x_8 = x_78;
goto _start;
}
}
else
{
uint8_t x_82; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_65);
if (x_82 == 0)
{
return x_65;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_65, 0);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_65);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
x_86 = lean_box(0);
x_32 = x_86;
goto block_62;
}
}
else
{
lean_object* x_87; 
lean_dec(x_28);
x_87 = lean_box(0);
x_32 = x_87;
goto block_62;
}
block_62:
{
lean_object* x_33; 
lean_dec(x_32);
x_33 = l_Lean_ConstantInfo_value_x3f(x_23);
lean_dec(x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_1);
x_34 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_34, 0, x_18);
x_35 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_10);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_42, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_18);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = l_Lean_Environment_getModuleIdxFor_x3f(x_17, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_47 = lean_box(0);
x_48 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4(x_1, x_44, x_46, x_25, x_21, x_19, x_13, x_10, x_26, x_47, x_4, x_5, x_6, x_7, x_29);
return x_48;
}
else
{
lean_dec(x_45);
if (x_3 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_1);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_13);
x_50 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_53, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_60 = lean_box(0);
x_61 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4(x_1, x_44, x_59, x_25, x_21, x_19, x_13, x_10, x_26, x_60, x_4, x_5, x_6, x_7, x_29);
return x_61;
}
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_27);
if (x_88 == 0)
{
return x_27;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_27, 0);
x_90 = lean_ctor_get(x_27, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_27);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_22);
if (x_92 == 0)
{
return x_22;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_22, 0);
x_94 = lean_ctor_get(x_22, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_22);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
x_96 = lean_ctor_get(x_20, 0);
lean_inc(x_96);
lean_dec(x_20);
x_97 = lean_box(0);
x_98 = l_Lean_mkConst(x_96, x_97);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_98);
x_99 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_98, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__5___boxed), 10, 3);
lean_closure_set(x_102, 0, x_10);
lean_closure_set(x_102, 1, x_1);
lean_closure_set(x_102, 2, x_98);
x_103 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_100, x_102, x_4, x_5, x_6, x_7, x_101);
return x_103;
}
else
{
uint8_t x_104; 
lean_dec(x_98);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_99);
if (x_104 == 0)
{
return x_99;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_99, 0);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_99);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_12);
lean_dec(x_1);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_10);
x_109 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_112, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_113;
}
}
case 1:
{
uint8_t x_114; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_9);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_9, 0);
lean_dec(x_115);
return x_9;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_9, 1);
lean_inc(x_116);
lean_dec(x_9);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_10);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
case 2:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_9, 1);
lean_inc(x_118);
lean_dec(x_9);
x_119 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_119) == 4)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_st_ref_get(x_7, x_118);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 2);
lean_inc(x_126);
x_127 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_126, x_124, x_120);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_inc(x_125);
x_128 = l_Lean_Name_append(x_120, x_125);
lean_inc(x_120);
x_129 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_120, x_4, x_5, x_6, x_7, x_123);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_ConstantInfo_type(x_130);
x_133 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_132);
x_134 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_132, x_133, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_138 = l_Lean_Expr_isConstOf(x_135, x_137);
if (x_138 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_171 = l_Lean_Expr_isConstOf(x_135, x_170);
lean_dec(x_135);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_172 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_136);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_1);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_175, 0, x_125);
x_176 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_177 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_179 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_10);
x_181 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_183 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_183, x_4, x_5, x_6, x_7, x_174);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_125);
lean_dec(x_10);
x_185 = lean_ctor_get(x_172, 1);
lean_inc(x_185);
lean_dec(x_172);
x_186 = lean_ctor_get(x_173, 0);
lean_inc(x_186);
lean_dec(x_173);
x_187 = 0;
x_2 = x_186;
x_3 = x_187;
x_8 = x_185;
goto _start;
}
}
else
{
uint8_t x_189; 
lean_dec(x_125);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_172);
if (x_189 == 0)
{
return x_172;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_172, 0);
x_191 = lean_ctor_get(x_172, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_172);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; 
x_193 = lean_box(0);
x_139 = x_193;
goto block_169;
}
}
else
{
lean_object* x_194; 
lean_dec(x_135);
x_194 = lean_box(0);
x_139 = x_194;
goto block_169;
}
block_169:
{
lean_object* x_140; 
lean_dec(x_139);
x_140 = l_Lean_ConstantInfo_value_x3f(x_130);
lean_dec(x_130);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_132);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_1);
x_141 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_141, 0, x_125);
x_142 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_146, 0, x_10);
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_149, x_4, x_5, x_6, x_7, x_136);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_125);
x_151 = lean_ctor_get(x_140, 0);
lean_inc(x_151);
lean_dec(x_140);
x_152 = l_Lean_Environment_getModuleIdxFor_x3f(x_124, x_120);
lean_dec(x_124);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_154 = lean_box(0);
x_155 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9(x_1, x_151, x_153, x_132, x_128, x_126, x_120, x_10, x_133, x_154, x_4, x_5, x_6, x_7, x_136);
return x_155;
}
else
{
lean_dec(x_152);
if (x_3 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_151);
lean_dec(x_132);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_10);
lean_dec(x_1);
x_156 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_156, 0, x_120);
x_157 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_158 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_160 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_160, x_4, x_5, x_6, x_7, x_136);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
return x_161;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_161);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_167 = lean_box(0);
x_168 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9(x_1, x_151, x_166, x_132, x_128, x_126, x_120, x_10, x_133, x_167, x_4, x_5, x_6, x_7, x_136);
return x_168;
}
}
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_134);
if (x_195 == 0)
{
return x_134;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_134, 0);
x_197 = lean_ctor_get(x_134, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_134);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_129);
if (x_199 == 0)
{
return x_129;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_129, 0);
x_201 = lean_ctor_get(x_129, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_129);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_120);
x_203 = lean_ctor_get(x_127, 0);
lean_inc(x_203);
lean_dec(x_127);
x_204 = lean_box(0);
x_205 = l_Lean_mkConst(x_203, x_204);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_205);
x_206 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_205, x_4, x_5, x_6, x_7, x_123);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__10___boxed), 10, 3);
lean_closure_set(x_209, 0, x_10);
lean_closure_set(x_209, 1, x_1);
lean_closure_set(x_209, 2, x_205);
x_210 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_207, x_209, x_4, x_5, x_6, x_7, x_208);
return x_210;
}
else
{
uint8_t x_211; 
lean_dec(x_205);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_119);
lean_dec(x_1);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_10);
x_216 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_217 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_219 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_219, x_4, x_5, x_6, x_7, x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_220;
}
}
case 3:
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_9, 1);
lean_inc(x_221);
lean_dec(x_9);
x_222 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_222) == 4)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_st_ref_get(x_7, x_221);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_1, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_1, 2);
lean_inc(x_229);
x_230 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_229, x_227, x_223);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_inc(x_228);
x_231 = l_Lean_Name_append(x_223, x_228);
lean_inc(x_223);
x_232 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_223, x_4, x_5, x_6, x_7, x_226);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_ConstantInfo_type(x_233);
x_236 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_235);
x_237 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_235, x_236, x_4, x_5, x_6, x_7, x_234);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_241 = l_Lean_Expr_isConstOf(x_238, x_240);
if (x_241 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_274 = l_Lean_Expr_isConstOf(x_238, x_273);
lean_dec(x_238);
if (x_274 == 0)
{
lean_object* x_275; 
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_223);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_275 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_239);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_1);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_278, 0, x_228);
x_279 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_280 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_282 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_283, 0, x_10);
x_284 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_286 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_286, x_4, x_5, x_6, x_7, x_277);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
lean_dec(x_228);
lean_dec(x_10);
x_288 = lean_ctor_get(x_275, 1);
lean_inc(x_288);
lean_dec(x_275);
x_289 = lean_ctor_get(x_276, 0);
lean_inc(x_289);
lean_dec(x_276);
x_290 = 0;
x_2 = x_289;
x_3 = x_290;
x_8 = x_288;
goto _start;
}
}
else
{
uint8_t x_292; 
lean_dec(x_228);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_275);
if (x_292 == 0)
{
return x_275;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_275, 0);
x_294 = lean_ctor_get(x_275, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_275);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; 
x_296 = lean_box(0);
x_242 = x_296;
goto block_272;
}
}
else
{
lean_object* x_297; 
lean_dec(x_238);
x_297 = lean_box(0);
x_242 = x_297;
goto block_272;
}
block_272:
{
lean_object* x_243; 
lean_dec(x_242);
x_243 = l_Lean_ConstantInfo_value_x3f(x_233);
lean_dec(x_233);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_235);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_223);
lean_dec(x_1);
x_244 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_244, 0, x_228);
x_245 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_246 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_248 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_249, 0, x_10);
x_250 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_252 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_252, x_4, x_5, x_6, x_7, x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_228);
x_254 = lean_ctor_get(x_243, 0);
lean_inc(x_254);
lean_dec(x_243);
x_255 = l_Lean_Environment_getModuleIdxFor_x3f(x_227, x_223);
lean_dec(x_227);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_257 = lean_box(0);
x_258 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14(x_1, x_254, x_256, x_235, x_231, x_229, x_223, x_10, x_236, x_257, x_4, x_5, x_6, x_7, x_239);
return x_258;
}
else
{
lean_dec(x_255);
if (x_3 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_dec(x_254);
lean_dec(x_235);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_10);
lean_dec(x_1);
x_259 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_259, 0, x_223);
x_260 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_261 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_263 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_263, x_4, x_5, x_6, x_7, x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
return x_264;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_264);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_270 = lean_box(0);
x_271 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14(x_1, x_254, x_269, x_235, x_231, x_229, x_223, x_10, x_236, x_270, x_4, x_5, x_6, x_7, x_239);
return x_271;
}
}
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_223);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_237);
if (x_298 == 0)
{
return x_237;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_237, 0);
x_300 = lean_ctor_get(x_237, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_237);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_223);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_232);
if (x_302 == 0)
{
return x_232;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_232, 0);
x_304 = lean_ctor_get(x_232, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_232);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_223);
x_306 = lean_ctor_get(x_230, 0);
lean_inc(x_306);
lean_dec(x_230);
x_307 = lean_box(0);
x_308 = l_Lean_mkConst(x_306, x_307);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_308);
x_309 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_308, x_4, x_5, x_6, x_7, x_226);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__15___boxed), 10, 3);
lean_closure_set(x_312, 0, x_10);
lean_closure_set(x_312, 1, x_1);
lean_closure_set(x_312, 2, x_308);
x_313 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_310, x_312, x_4, x_5, x_6, x_7, x_311);
return x_313;
}
else
{
uint8_t x_314; 
lean_dec(x_308);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_309);
if (x_314 == 0)
{
return x_309;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_309, 0);
x_316 = lean_ctor_get(x_309, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_309);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_222);
lean_dec(x_1);
x_318 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_318, 0, x_10);
x_319 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_320 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_322 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_322, x_4, x_5, x_6, x_7, x_221);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_323;
}
}
case 4:
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_9, 1);
lean_inc(x_324);
lean_dec(x_9);
x_325 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_325) == 4)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_st_ref_get(x_7, x_324);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_1, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_1, 2);
lean_inc(x_332);
x_333 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_332, x_330, x_326);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_inc(x_331);
x_334 = l_Lean_Name_append(x_326, x_331);
lean_inc(x_326);
x_335 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_326, x_4, x_5, x_6, x_7, x_329);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Lean_ConstantInfo_type(x_336);
x_339 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_338);
x_340 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_338, x_339, x_4, x_5, x_6, x_7, x_337);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_344 = l_Lean_Expr_isConstOf(x_341, x_343);
if (x_344 == 0)
{
lean_object* x_376; uint8_t x_377; 
x_376 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_377 = l_Lean_Expr_isConstOf(x_341, x_376);
lean_dec(x_341);
if (x_377 == 0)
{
lean_object* x_378; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_334);
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_326);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_378 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_342);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_1);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_381, 0, x_331);
x_382 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_383 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
x_384 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_385 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_386, 0, x_10);
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_389 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_389, x_4, x_5, x_6, x_7, x_380);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_331);
lean_dec(x_10);
x_391 = lean_ctor_get(x_378, 1);
lean_inc(x_391);
lean_dec(x_378);
x_392 = lean_ctor_get(x_379, 0);
lean_inc(x_392);
lean_dec(x_379);
x_393 = 0;
x_2 = x_392;
x_3 = x_393;
x_8 = x_391;
goto _start;
}
}
else
{
uint8_t x_395; 
lean_dec(x_331);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_395 = !lean_is_exclusive(x_378);
if (x_395 == 0)
{
return x_378;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_378, 0);
x_397 = lean_ctor_get(x_378, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_378);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
lean_object* x_399; 
x_399 = lean_box(0);
x_345 = x_399;
goto block_375;
}
}
else
{
lean_object* x_400; 
lean_dec(x_341);
x_400 = lean_box(0);
x_345 = x_400;
goto block_375;
}
block_375:
{
lean_object* x_346; 
lean_dec(x_345);
x_346 = l_Lean_ConstantInfo_value_x3f(x_336);
lean_dec(x_336);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_338);
lean_dec(x_334);
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_326);
lean_dec(x_1);
x_347 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_347, 0, x_331);
x_348 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_349 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
x_350 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_351 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_352, 0, x_10);
x_353 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_355 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_355, x_4, x_5, x_6, x_7, x_342);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_331);
x_357 = lean_ctor_get(x_346, 0);
lean_inc(x_357);
lean_dec(x_346);
x_358 = l_Lean_Environment_getModuleIdxFor_x3f(x_330, x_326);
lean_dec(x_330);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_360 = lean_box(0);
x_361 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19(x_1, x_357, x_359, x_338, x_334, x_332, x_326, x_10, x_339, x_360, x_4, x_5, x_6, x_7, x_342);
return x_361;
}
else
{
lean_dec(x_358);
if (x_3 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec(x_357);
lean_dec(x_338);
lean_dec(x_334);
lean_dec(x_332);
lean_dec(x_10);
lean_dec(x_1);
x_362 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_362, 0, x_326);
x_363 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_364 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_366 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_366, x_4, x_5, x_6, x_7, x_342);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
return x_367;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_367);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_373 = lean_box(0);
x_374 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19(x_1, x_357, x_372, x_338, x_334, x_332, x_326, x_10, x_339, x_373, x_4, x_5, x_6, x_7, x_342);
return x_374;
}
}
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_334);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_326);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_340);
if (x_401 == 0)
{
return x_340;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_340, 0);
x_403 = lean_ctor_get(x_340, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_340);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_334);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_326);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_335);
if (x_405 == 0)
{
return x_335;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_335, 0);
x_407 = lean_ctor_get(x_335, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_335);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_326);
x_409 = lean_ctor_get(x_333, 0);
lean_inc(x_409);
lean_dec(x_333);
x_410 = lean_box(0);
x_411 = l_Lean_mkConst(x_409, x_410);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_411);
x_412 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_411, x_4, x_5, x_6, x_7, x_329);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__20___boxed), 10, 3);
lean_closure_set(x_415, 0, x_10);
lean_closure_set(x_415, 1, x_1);
lean_closure_set(x_415, 2, x_411);
x_416 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_413, x_415, x_4, x_5, x_6, x_7, x_414);
return x_416;
}
else
{
uint8_t x_417; 
lean_dec(x_411);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_412);
if (x_417 == 0)
{
return x_412;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_412, 0);
x_419 = lean_ctor_get(x_412, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_412);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_325);
lean_dec(x_1);
x_421 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_421, 0, x_10);
x_422 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_423 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_421);
x_424 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_425 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
x_426 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_425, x_4, x_5, x_6, x_7, x_324);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_426;
}
}
case 5:
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_9, 1);
lean_inc(x_427);
lean_dec(x_9);
x_428 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_428) == 4)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
lean_dec(x_428);
x_430 = lean_st_ref_get(x_7, x_427);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_ctor_get(x_431, 0);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_1, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_1, 2);
lean_inc(x_435);
x_436 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_435, x_433, x_429);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; 
lean_inc(x_434);
x_437 = l_Lean_Name_append(x_429, x_434);
lean_inc(x_429);
x_438 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_429, x_4, x_5, x_6, x_7, x_432);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = l_Lean_ConstantInfo_type(x_439);
x_442 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_441);
x_443 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_441, x_442, x_4, x_5, x_6, x_7, x_440);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_447 = l_Lean_Expr_isConstOf(x_444, x_446);
if (x_447 == 0)
{
lean_object* x_479; uint8_t x_480; 
x_479 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_480 = l_Lean_Expr_isConstOf(x_444, x_479);
lean_dec(x_444);
if (x_480 == 0)
{
lean_object* x_481; 
lean_dec(x_441);
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_433);
lean_dec(x_429);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_481 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_445);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_1);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_484, 0, x_434);
x_485 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_486 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_484);
x_487 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_488 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_489, 0, x_10);
x_490 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_492 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
x_493 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_492, x_4, x_5, x_6, x_7, x_483);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
lean_dec(x_434);
lean_dec(x_10);
x_494 = lean_ctor_get(x_481, 1);
lean_inc(x_494);
lean_dec(x_481);
x_495 = lean_ctor_get(x_482, 0);
lean_inc(x_495);
lean_dec(x_482);
x_496 = 0;
x_2 = x_495;
x_3 = x_496;
x_8 = x_494;
goto _start;
}
}
else
{
uint8_t x_498; 
lean_dec(x_434);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_498 = !lean_is_exclusive(x_481);
if (x_498 == 0)
{
return x_481;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_481, 0);
x_500 = lean_ctor_get(x_481, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_481);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
else
{
lean_object* x_502; 
x_502 = lean_box(0);
x_448 = x_502;
goto block_478;
}
}
else
{
lean_object* x_503; 
lean_dec(x_444);
x_503 = lean_box(0);
x_448 = x_503;
goto block_478;
}
block_478:
{
lean_object* x_449; 
lean_dec(x_448);
x_449 = l_Lean_ConstantInfo_value_x3f(x_439);
lean_dec(x_439);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_441);
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_433);
lean_dec(x_429);
lean_dec(x_1);
x_450 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_450, 0, x_434);
x_451 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_452 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_450);
x_453 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_454 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_455, 0, x_10);
x_456 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
x_457 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_458 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
x_459 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_458, x_4, x_5, x_6, x_7, x_445);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_434);
x_460 = lean_ctor_get(x_449, 0);
lean_inc(x_460);
lean_dec(x_449);
x_461 = l_Lean_Environment_getModuleIdxFor_x3f(x_433, x_429);
lean_dec(x_433);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_463 = lean_box(0);
x_464 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24(x_1, x_460, x_462, x_441, x_437, x_435, x_429, x_10, x_442, x_463, x_4, x_5, x_6, x_7, x_445);
return x_464;
}
else
{
lean_dec(x_461);
if (x_3 == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
lean_dec(x_460);
lean_dec(x_441);
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_10);
lean_dec(x_1);
x_465 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_465, 0, x_429);
x_466 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_467 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_465);
x_468 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_469 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_469, x_4, x_5, x_6, x_7, x_445);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_471 = !lean_is_exclusive(x_470);
if (x_471 == 0)
{
return x_470;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_470, 0);
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_470);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_476 = lean_box(0);
x_477 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24(x_1, x_460, x_475, x_441, x_437, x_435, x_429, x_10, x_442, x_476, x_4, x_5, x_6, x_7, x_445);
return x_477;
}
}
}
}
}
else
{
uint8_t x_504; 
lean_dec(x_441);
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_429);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_504 = !lean_is_exclusive(x_443);
if (x_504 == 0)
{
return x_443;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_443, 0);
x_506 = lean_ctor_get(x_443, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_443);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
}
}
else
{
uint8_t x_508; 
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_429);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_508 = !lean_is_exclusive(x_438);
if (x_508 == 0)
{
return x_438;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_438, 0);
x_510 = lean_ctor_get(x_438, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_438);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_429);
x_512 = lean_ctor_get(x_436, 0);
lean_inc(x_512);
lean_dec(x_436);
x_513 = lean_box(0);
x_514 = l_Lean_mkConst(x_512, x_513);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_514);
x_515 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_514, x_4, x_5, x_6, x_7, x_432);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__25___boxed), 10, 3);
lean_closure_set(x_518, 0, x_10);
lean_closure_set(x_518, 1, x_1);
lean_closure_set(x_518, 2, x_514);
x_519 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_516, x_518, x_4, x_5, x_6, x_7, x_517);
return x_519;
}
else
{
uint8_t x_520; 
lean_dec(x_514);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_520 = !lean_is_exclusive(x_515);
if (x_520 == 0)
{
return x_515;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_515, 0);
x_522 = lean_ctor_get(x_515, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_515);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_428);
lean_dec(x_1);
x_524 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_524, 0, x_10);
x_525 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_526 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_524);
x_527 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_528 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
x_529 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_528, x_4, x_5, x_6, x_7, x_427);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_529;
}
}
case 6:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_9, 1);
lean_inc(x_530);
lean_dec(x_9);
x_531 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__26), 8, 1);
lean_closure_set(x_531, 0, x_1);
x_532 = l_Lean_Meta_lambdaLetTelescope___at_Lean_ParserCompiler_compileParserBody___spec__18___rarg(x_10, x_531, x_4, x_5, x_6, x_7, x_530);
return x_532;
}
case 7:
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_ctor_get(x_9, 1);
lean_inc(x_533);
lean_dec(x_9);
x_534 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_534) == 4)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
lean_dec(x_534);
x_536 = lean_st_ref_get(x_7, x_533);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get(x_1, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_1, 2);
lean_inc(x_541);
x_542 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_541, x_539, x_535);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; 
lean_inc(x_540);
x_543 = l_Lean_Name_append(x_535, x_540);
lean_inc(x_535);
x_544 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_535, x_4, x_5, x_6, x_7, x_538);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = l_Lean_ConstantInfo_type(x_545);
x_548 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_547);
x_549 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_547, x_548, x_4, x_5, x_6, x_7, x_546);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_553 = l_Lean_Expr_isConstOf(x_550, x_552);
if (x_553 == 0)
{
lean_object* x_585; uint8_t x_586; 
x_585 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_586 = l_Lean_Expr_isConstOf(x_550, x_585);
lean_dec(x_550);
if (x_586 == 0)
{
lean_object* x_587; 
lean_dec(x_547);
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_539);
lean_dec(x_535);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_587 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_551);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_1);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_590, 0, x_540);
x_591 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_592 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_590);
x_593 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_594 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
x_595 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_595, 0, x_10);
x_596 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
x_597 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_598 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
x_599 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_598, x_4, x_5, x_6, x_7, x_589);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_599;
}
else
{
lean_object* x_600; lean_object* x_601; uint8_t x_602; 
lean_dec(x_540);
lean_dec(x_10);
x_600 = lean_ctor_get(x_587, 1);
lean_inc(x_600);
lean_dec(x_587);
x_601 = lean_ctor_get(x_588, 0);
lean_inc(x_601);
lean_dec(x_588);
x_602 = 0;
x_2 = x_601;
x_3 = x_602;
x_8 = x_600;
goto _start;
}
}
else
{
uint8_t x_604; 
lean_dec(x_540);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_604 = !lean_is_exclusive(x_587);
if (x_604 == 0)
{
return x_587;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_587, 0);
x_606 = lean_ctor_get(x_587, 1);
lean_inc(x_606);
lean_inc(x_605);
lean_dec(x_587);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
return x_607;
}
}
}
else
{
lean_object* x_608; 
x_608 = lean_box(0);
x_554 = x_608;
goto block_584;
}
}
else
{
lean_object* x_609; 
lean_dec(x_550);
x_609 = lean_box(0);
x_554 = x_609;
goto block_584;
}
block_584:
{
lean_object* x_555; 
lean_dec(x_554);
x_555 = l_Lean_ConstantInfo_value_x3f(x_545);
lean_dec(x_545);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_547);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_539);
lean_dec(x_535);
lean_dec(x_1);
x_556 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_556, 0, x_540);
x_557 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_558 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_560 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
x_561 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_561, 0, x_10);
x_562 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
x_563 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_564 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
x_565 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_564, x_4, x_5, x_6, x_7, x_551);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_565;
}
else
{
lean_object* x_566; lean_object* x_567; 
lean_dec(x_540);
x_566 = lean_ctor_get(x_555, 0);
lean_inc(x_566);
lean_dec(x_555);
x_567 = l_Lean_Environment_getModuleIdxFor_x3f(x_539, x_535);
lean_dec(x_539);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_568 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_569 = lean_box(0);
x_570 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30(x_1, x_566, x_568, x_547, x_543, x_541, x_535, x_10, x_548, x_569, x_4, x_5, x_6, x_7, x_551);
return x_570;
}
else
{
lean_dec(x_567);
if (x_3 == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; 
lean_dec(x_566);
lean_dec(x_547);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_10);
lean_dec(x_1);
x_571 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_571, 0, x_535);
x_572 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_573 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_573, 1, x_571);
x_574 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_575 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
x_576 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_575, x_4, x_5, x_6, x_7, x_551);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_577 = !lean_is_exclusive(x_576);
if (x_577 == 0)
{
return x_576;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_576, 0);
x_579 = lean_ctor_get(x_576, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_576);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_582 = lean_box(0);
x_583 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30(x_1, x_566, x_581, x_547, x_543, x_541, x_535, x_10, x_548, x_582, x_4, x_5, x_6, x_7, x_551);
return x_583;
}
}
}
}
}
else
{
uint8_t x_610; 
lean_dec(x_547);
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_535);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_610 = !lean_is_exclusive(x_549);
if (x_610 == 0)
{
return x_549;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_549, 0);
x_612 = lean_ctor_get(x_549, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_549);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
else
{
uint8_t x_614; 
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_535);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_614 = !lean_is_exclusive(x_544);
if (x_614 == 0)
{
return x_544;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_544, 0);
x_616 = lean_ctor_get(x_544, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_544);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
return x_617;
}
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_535);
x_618 = lean_ctor_get(x_542, 0);
lean_inc(x_618);
lean_dec(x_542);
x_619 = lean_box(0);
x_620 = l_Lean_mkConst(x_618, x_619);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_620);
x_621 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_620, x_4, x_5, x_6, x_7, x_538);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__31___boxed), 10, 3);
lean_closure_set(x_624, 0, x_10);
lean_closure_set(x_624, 1, x_1);
lean_closure_set(x_624, 2, x_620);
x_625 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_622, x_624, x_4, x_5, x_6, x_7, x_623);
return x_625;
}
else
{
uint8_t x_626; 
lean_dec(x_620);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_626 = !lean_is_exclusive(x_621);
if (x_626 == 0)
{
return x_621;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_621, 0);
x_628 = lean_ctor_get(x_621, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_621);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
}
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
lean_dec(x_534);
lean_dec(x_1);
x_630 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_630, 0, x_10);
x_631 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_632 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_630);
x_633 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_634 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
x_635 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_634, x_4, x_5, x_6, x_7, x_533);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_635;
}
}
case 8:
{
lean_object* x_636; lean_object* x_637; 
x_636 = lean_ctor_get(x_9, 1);
lean_inc(x_636);
lean_dec(x_9);
x_637 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_637) == 4)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
lean_dec(x_637);
x_639 = lean_st_ref_get(x_7, x_636);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = lean_ctor_get(x_640, 0);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_ctor_get(x_1, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_1, 2);
lean_inc(x_644);
x_645 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_644, x_642, x_638);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; 
lean_inc(x_643);
x_646 = l_Lean_Name_append(x_638, x_643);
lean_inc(x_638);
x_647 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_638, x_4, x_5, x_6, x_7, x_641);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = l_Lean_ConstantInfo_type(x_648);
x_651 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_650);
x_652 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_650, x_651, x_4, x_5, x_6, x_7, x_649);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; lean_object* x_657; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_656 = l_Lean_Expr_isConstOf(x_653, x_655);
if (x_656 == 0)
{
lean_object* x_688; uint8_t x_689; 
x_688 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_689 = l_Lean_Expr_isConstOf(x_653, x_688);
lean_dec(x_653);
if (x_689 == 0)
{
lean_object* x_690; 
lean_dec(x_650);
lean_dec(x_648);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_638);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_690 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_654);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_1);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_693 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_693, 0, x_643);
x_694 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_695 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_693);
x_696 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_697 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
x_698 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_698, 0, x_10);
x_699 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
x_700 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_701 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_701, 0, x_699);
lean_ctor_set(x_701, 1, x_700);
x_702 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_701, x_4, x_5, x_6, x_7, x_692);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_702;
}
else
{
lean_object* x_703; lean_object* x_704; uint8_t x_705; 
lean_dec(x_643);
lean_dec(x_10);
x_703 = lean_ctor_get(x_690, 1);
lean_inc(x_703);
lean_dec(x_690);
x_704 = lean_ctor_get(x_691, 0);
lean_inc(x_704);
lean_dec(x_691);
x_705 = 0;
x_2 = x_704;
x_3 = x_705;
x_8 = x_703;
goto _start;
}
}
else
{
uint8_t x_707; 
lean_dec(x_643);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_707 = !lean_is_exclusive(x_690);
if (x_707 == 0)
{
return x_690;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_708 = lean_ctor_get(x_690, 0);
x_709 = lean_ctor_get(x_690, 1);
lean_inc(x_709);
lean_inc(x_708);
lean_dec(x_690);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
return x_710;
}
}
}
else
{
lean_object* x_711; 
x_711 = lean_box(0);
x_657 = x_711;
goto block_687;
}
}
else
{
lean_object* x_712; 
lean_dec(x_653);
x_712 = lean_box(0);
x_657 = x_712;
goto block_687;
}
block_687:
{
lean_object* x_658; 
lean_dec(x_657);
x_658 = l_Lean_ConstantInfo_value_x3f(x_648);
lean_dec(x_648);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_650);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_638);
lean_dec(x_1);
x_659 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_659, 0, x_643);
x_660 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_661 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_659);
x_662 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_663 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
x_664 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_664, 0, x_10);
x_665 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
x_666 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_667 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
x_668 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_667, x_4, x_5, x_6, x_7, x_654);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_668;
}
else
{
lean_object* x_669; lean_object* x_670; 
lean_dec(x_643);
x_669 = lean_ctor_get(x_658, 0);
lean_inc(x_669);
lean_dec(x_658);
x_670 = l_Lean_Environment_getModuleIdxFor_x3f(x_642, x_638);
lean_dec(x_642);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_672 = lean_box(0);
x_673 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35(x_1, x_669, x_671, x_650, x_646, x_644, x_638, x_10, x_651, x_672, x_4, x_5, x_6, x_7, x_654);
return x_673;
}
else
{
lean_dec(x_670);
if (x_3 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; 
lean_dec(x_669);
lean_dec(x_650);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_10);
lean_dec(x_1);
x_674 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_674, 0, x_638);
x_675 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_676 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_674);
x_677 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_678 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
x_679 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_678, x_4, x_5, x_6, x_7, x_654);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_680 = !lean_is_exclusive(x_679);
if (x_680 == 0)
{
return x_679;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_679, 0);
x_682 = lean_ctor_get(x_679, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_679);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
return x_683;
}
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_685 = lean_box(0);
x_686 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35(x_1, x_669, x_684, x_650, x_646, x_644, x_638, x_10, x_651, x_685, x_4, x_5, x_6, x_7, x_654);
return x_686;
}
}
}
}
}
else
{
uint8_t x_713; 
lean_dec(x_650);
lean_dec(x_648);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_642);
lean_dec(x_638);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_713 = !lean_is_exclusive(x_652);
if (x_713 == 0)
{
return x_652;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_652, 0);
x_715 = lean_ctor_get(x_652, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_652);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
uint8_t x_717; 
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_642);
lean_dec(x_638);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_717 = !lean_is_exclusive(x_647);
if (x_717 == 0)
{
return x_647;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_647, 0);
x_719 = lean_ctor_get(x_647, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_647);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_642);
lean_dec(x_638);
x_721 = lean_ctor_get(x_645, 0);
lean_inc(x_721);
lean_dec(x_645);
x_722 = lean_box(0);
x_723 = l_Lean_mkConst(x_721, x_722);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_723);
x_724 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_723, x_4, x_5, x_6, x_7, x_641);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__36___boxed), 10, 3);
lean_closure_set(x_727, 0, x_10);
lean_closure_set(x_727, 1, x_1);
lean_closure_set(x_727, 2, x_723);
x_728 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_725, x_727, x_4, x_5, x_6, x_7, x_726);
return x_728;
}
else
{
uint8_t x_729; 
lean_dec(x_723);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_729 = !lean_is_exclusive(x_724);
if (x_729 == 0)
{
return x_724;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_724, 0);
x_731 = lean_ctor_get(x_724, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_724);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_637);
lean_dec(x_1);
x_733 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_733, 0, x_10);
x_734 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_735 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_733);
x_736 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_737 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
x_738 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_737, x_4, x_5, x_6, x_7, x_636);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_738;
}
}
case 9:
{
lean_object* x_739; lean_object* x_740; 
x_739 = lean_ctor_get(x_9, 1);
lean_inc(x_739);
lean_dec(x_9);
x_740 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_740) == 4)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
lean_dec(x_740);
x_742 = lean_st_ref_get(x_7, x_739);
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = lean_ctor_get(x_743, 0);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_ctor_get(x_1, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_1, 2);
lean_inc(x_747);
x_748 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_747, x_745, x_741);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; 
lean_inc(x_746);
x_749 = l_Lean_Name_append(x_741, x_746);
lean_inc(x_741);
x_750 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_741, x_4, x_5, x_6, x_7, x_744);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_753 = l_Lean_ConstantInfo_type(x_751);
x_754 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_753);
x_755 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_753, x_754, x_4, x_5, x_6, x_7, x_752);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; lean_object* x_760; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
x_758 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_759 = l_Lean_Expr_isConstOf(x_756, x_758);
if (x_759 == 0)
{
lean_object* x_791; uint8_t x_792; 
x_791 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_792 = l_Lean_Expr_isConstOf(x_756, x_791);
lean_dec(x_756);
if (x_792 == 0)
{
lean_object* x_793; 
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_749);
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_741);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_793 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_757);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_1);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_796, 0, x_746);
x_797 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_798 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_796);
x_799 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_800 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_801, 0, x_10);
x_802 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
x_803 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_804 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
x_805 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_804, x_4, x_5, x_6, x_7, x_795);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_805;
}
else
{
lean_object* x_806; lean_object* x_807; uint8_t x_808; 
lean_dec(x_746);
lean_dec(x_10);
x_806 = lean_ctor_get(x_793, 1);
lean_inc(x_806);
lean_dec(x_793);
x_807 = lean_ctor_get(x_794, 0);
lean_inc(x_807);
lean_dec(x_794);
x_808 = 0;
x_2 = x_807;
x_3 = x_808;
x_8 = x_806;
goto _start;
}
}
else
{
uint8_t x_810; 
lean_dec(x_746);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_810 = !lean_is_exclusive(x_793);
if (x_810 == 0)
{
return x_793;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_811 = lean_ctor_get(x_793, 0);
x_812 = lean_ctor_get(x_793, 1);
lean_inc(x_812);
lean_inc(x_811);
lean_dec(x_793);
x_813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_813, 0, x_811);
lean_ctor_set(x_813, 1, x_812);
return x_813;
}
}
}
else
{
lean_object* x_814; 
x_814 = lean_box(0);
x_760 = x_814;
goto block_790;
}
}
else
{
lean_object* x_815; 
lean_dec(x_756);
x_815 = lean_box(0);
x_760 = x_815;
goto block_790;
}
block_790:
{
lean_object* x_761; 
lean_dec(x_760);
x_761 = l_Lean_ConstantInfo_value_x3f(x_751);
lean_dec(x_751);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_753);
lean_dec(x_749);
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_741);
lean_dec(x_1);
x_762 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_762, 0, x_746);
x_763 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_764 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_762);
x_765 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_766 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
x_767 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_767, 0, x_10);
x_768 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
x_769 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_770 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
x_771 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_770, x_4, x_5, x_6, x_7, x_757);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_771;
}
else
{
lean_object* x_772; lean_object* x_773; 
lean_dec(x_746);
x_772 = lean_ctor_get(x_761, 0);
lean_inc(x_772);
lean_dec(x_761);
x_773 = l_Lean_Environment_getModuleIdxFor_x3f(x_745, x_741);
lean_dec(x_745);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_775 = lean_box(0);
x_776 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40(x_1, x_772, x_774, x_753, x_749, x_747, x_741, x_10, x_754, x_775, x_4, x_5, x_6, x_7, x_757);
return x_776;
}
else
{
lean_dec(x_773);
if (x_3 == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; 
lean_dec(x_772);
lean_dec(x_753);
lean_dec(x_749);
lean_dec(x_747);
lean_dec(x_10);
lean_dec(x_1);
x_777 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_777, 0, x_741);
x_778 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_779 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_779, 0, x_778);
lean_ctor_set(x_779, 1, x_777);
x_780 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_781 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_781, 0, x_779);
lean_ctor_set(x_781, 1, x_780);
x_782 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_781, x_4, x_5, x_6, x_7, x_757);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_783 = !lean_is_exclusive(x_782);
if (x_783 == 0)
{
return x_782;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_782, 0);
x_785 = lean_ctor_get(x_782, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_782);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_788 = lean_box(0);
x_789 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40(x_1, x_772, x_787, x_753, x_749, x_747, x_741, x_10, x_754, x_788, x_4, x_5, x_6, x_7, x_757);
return x_789;
}
}
}
}
}
else
{
uint8_t x_816; 
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_749);
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_741);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_816 = !lean_is_exclusive(x_755);
if (x_816 == 0)
{
return x_755;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_755, 0);
x_818 = lean_ctor_get(x_755, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_755);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
return x_819;
}
}
}
else
{
uint8_t x_820; 
lean_dec(x_749);
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_741);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_820 = !lean_is_exclusive(x_750);
if (x_820 == 0)
{
return x_750;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_750, 0);
x_822 = lean_ctor_get(x_750, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_750);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_741);
x_824 = lean_ctor_get(x_748, 0);
lean_inc(x_824);
lean_dec(x_748);
x_825 = lean_box(0);
x_826 = l_Lean_mkConst(x_824, x_825);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_826);
x_827 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_826, x_4, x_5, x_6, x_7, x_744);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
x_830 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__41___boxed), 10, 3);
lean_closure_set(x_830, 0, x_10);
lean_closure_set(x_830, 1, x_1);
lean_closure_set(x_830, 2, x_826);
x_831 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_828, x_830, x_4, x_5, x_6, x_7, x_829);
return x_831;
}
else
{
uint8_t x_832; 
lean_dec(x_826);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_832 = !lean_is_exclusive(x_827);
if (x_832 == 0)
{
return x_827;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_833 = lean_ctor_get(x_827, 0);
x_834 = lean_ctor_get(x_827, 1);
lean_inc(x_834);
lean_inc(x_833);
lean_dec(x_827);
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_833);
lean_ctor_set(x_835, 1, x_834);
return x_835;
}
}
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_740);
lean_dec(x_1);
x_836 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_836, 0, x_10);
x_837 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_838 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_836);
x_839 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_840 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_840, 0, x_838);
lean_ctor_set(x_840, 1, x_839);
x_841 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_840, x_4, x_5, x_6, x_7, x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_841;
}
}
case 10:
{
lean_object* x_842; lean_object* x_843; 
x_842 = lean_ctor_get(x_9, 1);
lean_inc(x_842);
lean_dec(x_9);
x_843 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_843) == 4)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
lean_dec(x_843);
x_845 = lean_st_ref_get(x_7, x_842);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
lean_dec(x_846);
x_849 = lean_ctor_get(x_1, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_1, 2);
lean_inc(x_850);
x_851 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_850, x_848, x_844);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; 
lean_inc(x_849);
x_852 = l_Lean_Name_append(x_844, x_849);
lean_inc(x_844);
x_853 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_844, x_4, x_5, x_6, x_7, x_847);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
x_856 = l_Lean_ConstantInfo_type(x_854);
x_857 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_856);
x_858 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_856, x_857, x_4, x_5, x_6, x_7, x_855);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; uint8_t x_862; lean_object* x_863; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_862 = l_Lean_Expr_isConstOf(x_859, x_861);
if (x_862 == 0)
{
lean_object* x_894; uint8_t x_895; 
x_894 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_895 = l_Lean_Expr_isConstOf(x_859, x_894);
lean_dec(x_859);
if (x_895 == 0)
{
lean_object* x_896; 
lean_dec(x_856);
lean_dec(x_854);
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_844);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_896 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_860);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; 
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_1);
x_898 = lean_ctor_get(x_896, 1);
lean_inc(x_898);
lean_dec(x_896);
x_899 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_899, 0, x_849);
x_900 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_901 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_901, 0, x_900);
lean_ctor_set(x_901, 1, x_899);
x_902 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_903 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_903, 0, x_901);
lean_ctor_set(x_903, 1, x_902);
x_904 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_904, 0, x_10);
x_905 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
x_906 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_907 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_907, 0, x_905);
lean_ctor_set(x_907, 1, x_906);
x_908 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_907, x_4, x_5, x_6, x_7, x_898);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_908;
}
else
{
lean_object* x_909; lean_object* x_910; uint8_t x_911; 
lean_dec(x_849);
lean_dec(x_10);
x_909 = lean_ctor_get(x_896, 1);
lean_inc(x_909);
lean_dec(x_896);
x_910 = lean_ctor_get(x_897, 0);
lean_inc(x_910);
lean_dec(x_897);
x_911 = 0;
x_2 = x_910;
x_3 = x_911;
x_8 = x_909;
goto _start;
}
}
else
{
uint8_t x_913; 
lean_dec(x_849);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_913 = !lean_is_exclusive(x_896);
if (x_913 == 0)
{
return x_896;
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_914 = lean_ctor_get(x_896, 0);
x_915 = lean_ctor_get(x_896, 1);
lean_inc(x_915);
lean_inc(x_914);
lean_dec(x_896);
x_916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_916, 0, x_914);
lean_ctor_set(x_916, 1, x_915);
return x_916;
}
}
}
else
{
lean_object* x_917; 
x_917 = lean_box(0);
x_863 = x_917;
goto block_893;
}
}
else
{
lean_object* x_918; 
lean_dec(x_859);
x_918 = lean_box(0);
x_863 = x_918;
goto block_893;
}
block_893:
{
lean_object* x_864; 
lean_dec(x_863);
x_864 = l_Lean_ConstantInfo_value_x3f(x_854);
lean_dec(x_854);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec(x_856);
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_1);
x_865 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_865, 0, x_849);
x_866 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_867 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_867, 0, x_866);
lean_ctor_set(x_867, 1, x_865);
x_868 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_869 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_868);
x_870 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_870, 0, x_10);
x_871 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_871, 0, x_869);
lean_ctor_set(x_871, 1, x_870);
x_872 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_873 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_873, 1, x_872);
x_874 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_873, x_4, x_5, x_6, x_7, x_860);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_874;
}
else
{
lean_object* x_875; lean_object* x_876; 
lean_dec(x_849);
x_875 = lean_ctor_get(x_864, 0);
lean_inc(x_875);
lean_dec(x_864);
x_876 = l_Lean_Environment_getModuleIdxFor_x3f(x_848, x_844);
lean_dec(x_848);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_878 = lean_box(0);
x_879 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45(x_1, x_875, x_877, x_856, x_852, x_850, x_844, x_10, x_857, x_878, x_4, x_5, x_6, x_7, x_860);
return x_879;
}
else
{
lean_dec(x_876);
if (x_3 == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; 
lean_dec(x_875);
lean_dec(x_856);
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_10);
lean_dec(x_1);
x_880 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_880, 0, x_844);
x_881 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_882 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_880);
x_883 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_884 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_884, 0, x_882);
lean_ctor_set(x_884, 1, x_883);
x_885 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_884, x_4, x_5, x_6, x_7, x_860);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_886 = !lean_is_exclusive(x_885);
if (x_886 == 0)
{
return x_885;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_887 = lean_ctor_get(x_885, 0);
x_888 = lean_ctor_get(x_885, 1);
lean_inc(x_888);
lean_inc(x_887);
lean_dec(x_885);
x_889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_889, 0, x_887);
lean_ctor_set(x_889, 1, x_888);
return x_889;
}
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_891 = lean_box(0);
x_892 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45(x_1, x_875, x_890, x_856, x_852, x_850, x_844, x_10, x_857, x_891, x_4, x_5, x_6, x_7, x_860);
return x_892;
}
}
}
}
}
else
{
uint8_t x_919; 
lean_dec(x_856);
lean_dec(x_854);
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_919 = !lean_is_exclusive(x_858);
if (x_919 == 0)
{
return x_858;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_858, 0);
x_921 = lean_ctor_get(x_858, 1);
lean_inc(x_921);
lean_inc(x_920);
lean_dec(x_858);
x_922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
return x_922;
}
}
}
else
{
uint8_t x_923; 
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_923 = !lean_is_exclusive(x_853);
if (x_923 == 0)
{
return x_853;
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_924 = lean_ctor_get(x_853, 0);
x_925 = lean_ctor_get(x_853, 1);
lean_inc(x_925);
lean_inc(x_924);
lean_dec(x_853);
x_926 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_926, 0, x_924);
lean_ctor_set(x_926, 1, x_925);
return x_926;
}
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_844);
x_927 = lean_ctor_get(x_851, 0);
lean_inc(x_927);
lean_dec(x_851);
x_928 = lean_box(0);
x_929 = l_Lean_mkConst(x_927, x_928);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_929);
x_930 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_929, x_4, x_5, x_6, x_7, x_847);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_933 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__46___boxed), 10, 3);
lean_closure_set(x_933, 0, x_10);
lean_closure_set(x_933, 1, x_1);
lean_closure_set(x_933, 2, x_929);
x_934 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_931, x_933, x_4, x_5, x_6, x_7, x_932);
return x_934;
}
else
{
uint8_t x_935; 
lean_dec(x_929);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_935 = !lean_is_exclusive(x_930);
if (x_935 == 0)
{
return x_930;
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_930, 0);
x_937 = lean_ctor_get(x_930, 1);
lean_inc(x_937);
lean_inc(x_936);
lean_dec(x_930);
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set(x_938, 1, x_937);
return x_938;
}
}
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_843);
lean_dec(x_1);
x_939 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_939, 0, x_10);
x_940 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_941 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_939);
x_942 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_943 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_943, 0, x_941);
lean_ctor_set(x_943, 1, x_942);
x_944 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_943, x_4, x_5, x_6, x_7, x_842);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_944;
}
}
case 11:
{
lean_object* x_945; lean_object* x_946; 
x_945 = lean_ctor_get(x_9, 1);
lean_inc(x_945);
lean_dec(x_9);
x_946 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_946) == 4)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
lean_dec(x_946);
x_948 = lean_st_ref_get(x_7, x_945);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_ctor_get(x_949, 0);
lean_inc(x_951);
lean_dec(x_949);
x_952 = lean_ctor_get(x_1, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_1, 2);
lean_inc(x_953);
x_954 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_953, x_951, x_947);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; 
lean_inc(x_952);
x_955 = l_Lean_Name_append(x_947, x_952);
lean_inc(x_947);
x_956 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_947, x_4, x_5, x_6, x_7, x_950);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
x_959 = l_Lean_ConstantInfo_type(x_957);
x_960 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_959);
x_961 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_959, x_960, x_4, x_5, x_6, x_7, x_958);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; lean_object* x_966; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_965 = l_Lean_Expr_isConstOf(x_962, x_964);
if (x_965 == 0)
{
lean_object* x_997; uint8_t x_998; 
x_997 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_998 = l_Lean_Expr_isConstOf(x_962, x_997);
lean_dec(x_962);
if (x_998 == 0)
{
lean_object* x_999; 
lean_dec(x_959);
lean_dec(x_957);
lean_dec(x_955);
lean_dec(x_953);
lean_dec(x_951);
lean_dec(x_947);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_999 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_963);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; 
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
if (lean_obj_tag(x_1000) == 0)
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_1);
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
lean_dec(x_999);
x_1002 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1002, 0, x_952);
x_1003 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_1004 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_1002);
x_1005 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_1006 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1006, 0, x_1004);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1007, 0, x_10);
x_1008 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1008, 0, x_1006);
lean_ctor_set(x_1008, 1, x_1007);
x_1009 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_1010 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1010, 0, x_1008);
lean_ctor_set(x_1010, 1, x_1009);
x_1011 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1010, x_4, x_5, x_6, x_7, x_1001);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1011;
}
else
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
lean_dec(x_952);
lean_dec(x_10);
x_1012 = lean_ctor_get(x_999, 1);
lean_inc(x_1012);
lean_dec(x_999);
x_1013 = lean_ctor_get(x_1000, 0);
lean_inc(x_1013);
lean_dec(x_1000);
x_1014 = 0;
x_2 = x_1013;
x_3 = x_1014;
x_8 = x_1012;
goto _start;
}
}
else
{
uint8_t x_1016; 
lean_dec(x_952);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1016 = !lean_is_exclusive(x_999);
if (x_1016 == 0)
{
return x_999;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_999, 0);
x_1018 = lean_ctor_get(x_999, 1);
lean_inc(x_1018);
lean_inc(x_1017);
lean_dec(x_999);
x_1019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1019, 0, x_1017);
lean_ctor_set(x_1019, 1, x_1018);
return x_1019;
}
}
}
else
{
lean_object* x_1020; 
x_1020 = lean_box(0);
x_966 = x_1020;
goto block_996;
}
}
else
{
lean_object* x_1021; 
lean_dec(x_962);
x_1021 = lean_box(0);
x_966 = x_1021;
goto block_996;
}
block_996:
{
lean_object* x_967; 
lean_dec(x_966);
x_967 = l_Lean_ConstantInfo_value_x3f(x_957);
lean_dec(x_957);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_959);
lean_dec(x_955);
lean_dec(x_953);
lean_dec(x_951);
lean_dec(x_947);
lean_dec(x_1);
x_968 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_968, 0, x_952);
x_969 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_970 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_968);
x_971 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_972 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_972, 0, x_970);
lean_ctor_set(x_972, 1, x_971);
x_973 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_973, 0, x_10);
x_974 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_974, 0, x_972);
lean_ctor_set(x_974, 1, x_973);
x_975 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_976 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_976, 0, x_974);
lean_ctor_set(x_976, 1, x_975);
x_977 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_976, x_4, x_5, x_6, x_7, x_963);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_977;
}
else
{
lean_object* x_978; lean_object* x_979; 
lean_dec(x_952);
x_978 = lean_ctor_get(x_967, 0);
lean_inc(x_978);
lean_dec(x_967);
x_979 = l_Lean_Environment_getModuleIdxFor_x3f(x_951, x_947);
lean_dec(x_951);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_980 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_981 = lean_box(0);
x_982 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50(x_1, x_978, x_980, x_959, x_955, x_953, x_947, x_10, x_960, x_981, x_4, x_5, x_6, x_7, x_963);
return x_982;
}
else
{
lean_dec(x_979);
if (x_3 == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; uint8_t x_989; 
lean_dec(x_978);
lean_dec(x_959);
lean_dec(x_955);
lean_dec(x_953);
lean_dec(x_10);
lean_dec(x_1);
x_983 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_983, 0, x_947);
x_984 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_985 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_983);
x_986 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_987 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_987, 0, x_985);
lean_ctor_set(x_987, 1, x_986);
x_988 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_987, x_4, x_5, x_6, x_7, x_963);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_989 = !lean_is_exclusive(x_988);
if (x_989 == 0)
{
return x_988;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_988, 0);
x_991 = lean_ctor_get(x_988, 1);
lean_inc(x_991);
lean_inc(x_990);
lean_dec(x_988);
x_992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
return x_992;
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_994 = lean_box(0);
x_995 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50(x_1, x_978, x_993, x_959, x_955, x_953, x_947, x_10, x_960, x_994, x_4, x_5, x_6, x_7, x_963);
return x_995;
}
}
}
}
}
else
{
uint8_t x_1022; 
lean_dec(x_959);
lean_dec(x_957);
lean_dec(x_955);
lean_dec(x_953);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_947);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1022 = !lean_is_exclusive(x_961);
if (x_1022 == 0)
{
return x_961;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_961, 0);
x_1024 = lean_ctor_get(x_961, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_961);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
else
{
uint8_t x_1026; 
lean_dec(x_955);
lean_dec(x_953);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_947);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1026 = !lean_is_exclusive(x_956);
if (x_1026 == 0)
{
return x_956;
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1027 = lean_ctor_get(x_956, 0);
x_1028 = lean_ctor_get(x_956, 1);
lean_inc(x_1028);
lean_inc(x_1027);
lean_dec(x_956);
x_1029 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1029, 0, x_1027);
lean_ctor_set(x_1029, 1, x_1028);
return x_1029;
}
}
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_953);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_947);
x_1030 = lean_ctor_get(x_954, 0);
lean_inc(x_1030);
lean_dec(x_954);
x_1031 = lean_box(0);
x_1032 = l_Lean_mkConst(x_1030, x_1031);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1032);
x_1033 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1032, x_4, x_5, x_6, x_7, x_950);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1033, 1);
lean_inc(x_1035);
lean_dec(x_1033);
x_1036 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__51___boxed), 10, 3);
lean_closure_set(x_1036, 0, x_10);
lean_closure_set(x_1036, 1, x_1);
lean_closure_set(x_1036, 2, x_1032);
x_1037 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_1034, x_1036, x_4, x_5, x_6, x_7, x_1035);
return x_1037;
}
else
{
uint8_t x_1038; 
lean_dec(x_1032);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1038 = !lean_is_exclusive(x_1033);
if (x_1038 == 0)
{
return x_1033;
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_1033, 0);
x_1040 = lean_ctor_get(x_1033, 1);
lean_inc(x_1040);
lean_inc(x_1039);
lean_dec(x_1033);
x_1041 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1041, 0, x_1039);
lean_ctor_set(x_1041, 1, x_1040);
return x_1041;
}
}
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_946);
lean_dec(x_1);
x_1042 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1042, 0, x_10);
x_1043 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_1044 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_1042);
x_1045 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_1046 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1046, 0, x_1044);
lean_ctor_set(x_1046, 1, x_1045);
x_1047 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1046, x_4, x_5, x_6, x_7, x_945);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1047;
}
}
default: 
{
lean_object* x_1048; lean_object* x_1049; 
x_1048 = lean_ctor_get(x_9, 1);
lean_inc(x_1048);
lean_dec(x_9);
x_1049 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_1049) == 4)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
lean_dec(x_1049);
x_1051 = lean_st_ref_get(x_7, x_1048);
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
lean_dec(x_1051);
x_1054 = lean_ctor_get(x_1052, 0);
lean_inc(x_1054);
lean_dec(x_1052);
x_1055 = lean_ctor_get(x_1, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1, 2);
lean_inc(x_1056);
x_1057 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1056, x_1054, x_1050);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; 
lean_inc(x_1055);
x_1058 = l_Lean_Name_append(x_1050, x_1055);
lean_inc(x_1050);
x_1059 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1050, x_4, x_5, x_6, x_7, x_1053);
if (lean_obj_tag(x_1059) == 0)
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1059, 1);
lean_inc(x_1061);
lean_dec(x_1059);
x_1062 = l_Lean_ConstantInfo_type(x_1060);
x_1063 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1062);
x_1064 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_1062, x_1063, x_4, x_5, x_6, x_7, x_1061);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; uint8_t x_1068; lean_object* x_1069; 
x_1065 = lean_ctor_get(x_1064, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1064, 1);
lean_inc(x_1066);
lean_dec(x_1064);
x_1067 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_1068 = l_Lean_Expr_isConstOf(x_1065, x_1067);
if (x_1068 == 0)
{
lean_object* x_1100; uint8_t x_1101; 
x_1100 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_1101 = l_Lean_Expr_isConstOf(x_1065, x_1100);
lean_dec(x_1065);
if (x_1101 == 0)
{
lean_object* x_1102; 
lean_dec(x_1062);
lean_dec(x_1060);
lean_dec(x_1058);
lean_dec(x_1056);
lean_dec(x_1054);
lean_dec(x_1050);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_1102 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_10, x_4, x_5, x_6, x_7, x_1066);
if (lean_obj_tag(x_1102) == 0)
{
lean_object* x_1103; 
x_1103 = lean_ctor_get(x_1102, 0);
lean_inc(x_1103);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1);
x_1104 = lean_ctor_get(x_1102, 1);
lean_inc(x_1104);
lean_dec(x_1102);
x_1105 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1105, 0, x_1055);
x_1106 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_1107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1107, 0, x_1106);
lean_ctor_set(x_1107, 1, x_1105);
x_1108 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__13;
x_1109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1109, 0, x_1107);
lean_ctor_set(x_1109, 1, x_1108);
x_1110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1110, 0, x_10);
x_1111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
x_1112 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_1113 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
x_1114 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1113, x_4, x_5, x_6, x_7, x_1104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1114;
}
else
{
lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; 
lean_dec(x_1055);
lean_dec(x_10);
x_1115 = lean_ctor_get(x_1102, 1);
lean_inc(x_1115);
lean_dec(x_1102);
x_1116 = lean_ctor_get(x_1103, 0);
lean_inc(x_1116);
lean_dec(x_1103);
x_1117 = 0;
x_2 = x_1116;
x_3 = x_1117;
x_8 = x_1115;
goto _start;
}
}
else
{
uint8_t x_1119; 
lean_dec(x_1055);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1119 = !lean_is_exclusive(x_1102);
if (x_1119 == 0)
{
return x_1102;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1120 = lean_ctor_get(x_1102, 0);
x_1121 = lean_ctor_get(x_1102, 1);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1102);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set(x_1122, 1, x_1121);
return x_1122;
}
}
}
else
{
lean_object* x_1123; 
x_1123 = lean_box(0);
x_1069 = x_1123;
goto block_1099;
}
}
else
{
lean_object* x_1124; 
lean_dec(x_1065);
x_1124 = lean_box(0);
x_1069 = x_1124;
goto block_1099;
}
block_1099:
{
lean_object* x_1070; 
lean_dec(x_1069);
x_1070 = l_Lean_ConstantInfo_value_x3f(x_1060);
lean_dec(x_1060);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_1062);
lean_dec(x_1058);
lean_dec(x_1056);
lean_dec(x_1054);
lean_dec(x_1050);
lean_dec(x_1);
x_1071 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1071, 0, x_1055);
x_1072 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__5;
x_1073 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1073, 0, x_1072);
lean_ctor_set(x_1073, 1, x_1071);
x_1074 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__7;
x_1075 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1075, 0, x_1073);
lean_ctor_set(x_1075, 1, x_1074);
x_1076 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1076, 0, x_10);
x_1077 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1077, 0, x_1075);
lean_ctor_set(x_1077, 1, x_1076);
x_1078 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_1079 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
x_1080 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1079, x_4, x_5, x_6, x_7, x_1066);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1080;
}
else
{
lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_1055);
x_1081 = lean_ctor_get(x_1070, 0);
lean_inc(x_1081);
lean_dec(x_1070);
x_1082 = l_Lean_Environment_getModuleIdxFor_x3f(x_1054, x_1050);
lean_dec(x_1054);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1083 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_1084 = lean_box(0);
x_1085 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55(x_1, x_1081, x_1083, x_1062, x_1058, x_1056, x_1050, x_10, x_1063, x_1084, x_4, x_5, x_6, x_7, x_1066);
return x_1085;
}
else
{
lean_dec(x_1082);
if (x_3 == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; uint8_t x_1092; 
lean_dec(x_1081);
lean_dec(x_1062);
lean_dec(x_1058);
lean_dec(x_1056);
lean_dec(x_10);
lean_dec(x_1);
x_1086 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1086, 0, x_1050);
x_1087 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__9;
x_1088 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1088, 0, x_1087);
lean_ctor_set(x_1088, 1, x_1086);
x_1089 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__11;
x_1090 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1090, 0, x_1088);
lean_ctor_set(x_1090, 1, x_1089);
x_1091 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1090, x_4, x_5, x_6, x_7, x_1066);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1092 = !lean_is_exclusive(x_1091);
if (x_1092 == 0)
{
return x_1091;
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1093 = lean_ctor_get(x_1091, 0);
x_1094 = lean_ctor_get(x_1091, 1);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_1091);
x_1095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1095, 0, x_1093);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_1097 = lean_box(0);
x_1098 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55(x_1, x_1081, x_1096, x_1062, x_1058, x_1056, x_1050, x_10, x_1063, x_1097, x_4, x_5, x_6, x_7, x_1066);
return x_1098;
}
}
}
}
}
else
{
uint8_t x_1125; 
lean_dec(x_1062);
lean_dec(x_1060);
lean_dec(x_1058);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_1054);
lean_dec(x_1050);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1125 = !lean_is_exclusive(x_1064);
if (x_1125 == 0)
{
return x_1064;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1064, 0);
x_1127 = lean_ctor_get(x_1064, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1064);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
}
else
{
uint8_t x_1129; 
lean_dec(x_1058);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_1054);
lean_dec(x_1050);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1129 = !lean_is_exclusive(x_1059);
if (x_1129 == 0)
{
return x_1059;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1059, 0);
x_1131 = lean_ctor_get(x_1059, 1);
lean_inc(x_1131);
lean_inc(x_1130);
lean_dec(x_1059);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_1054);
lean_dec(x_1050);
x_1133 = lean_ctor_get(x_1057, 0);
lean_inc(x_1133);
lean_dec(x_1057);
x_1134 = lean_box(0);
x_1135 = l_Lean_mkConst(x_1133, x_1134);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1135);
x_1136 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1135, x_4, x_5, x_6, x_7, x_1053);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1136, 1);
lean_inc(x_1138);
lean_dec(x_1136);
x_1139 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___lambda__56___boxed), 10, 3);
lean_closure_set(x_1139, 0, x_10);
lean_closure_set(x_1139, 1, x_1);
lean_closure_set(x_1139, 2, x_1135);
x_1140 = l_Lean_Meta_forallTelescope___at_Lean_ParserCompiler_compileParserBody___spec__1___rarg(x_1137, x_1139, x_4, x_5, x_6, x_7, x_1138);
return x_1140;
}
else
{
uint8_t x_1141; 
lean_dec(x_1135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1141 = !lean_is_exclusive(x_1136);
if (x_1141 == 0)
{
return x_1136;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1142 = lean_ctor_get(x_1136, 0);
x_1143 = lean_ctor_get(x_1136, 1);
lean_inc(x_1143);
lean_inc(x_1142);
lean_dec(x_1136);
x_1144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1144, 0, x_1142);
lean_ctor_set(x_1144, 1, x_1143);
return x_1144;
}
}
}
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1049);
lean_dec(x_1);
x_1145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1145, 0, x_10);
x_1146 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__2;
x_1147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1147, 0, x_1146);
lean_ctor_set(x_1147, 1, x_1145);
x_1148 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_1149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set(x_1149, 1, x_1148);
x_1150 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1149, x_4, x_5, x_6, x_7, x_1048);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1150;
}
}
}
}
else
{
uint8_t x_1151; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1151 = !lean_is_exclusive(x_9);
if (x_1151 == 0)
{
return x_9;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_9, 0);
x_1153 = lean_ctor_get(x_9, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_9);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__12___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__16___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkLambdaFVars___at_Lean_ParserCompiler_compileParserBody___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__20___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__21___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__23___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__24___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__26___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__27___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__29___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__30___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__32___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__33___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_ParserCompiler_compileParserBody___spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__35___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__36___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__30(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__36(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__37(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__38(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__40(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__41(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__42(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__43(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__45(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__46(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__47(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__48(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__50(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__51(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__52(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__53(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__55(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___lambda__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ParserCompiler_compileParserBody___rarg___lambda__56(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ParserCompiler_compileParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParser_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_CoreM___instance__2___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_compileParser___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__1___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserCompiler");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserCompiler.compileParser");
return x_1;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ParserCompiler_compileParser___rarg___closed__3;
x_2 = l_Lean_ParserCompiler_compileParser___rarg___closed__4;
x_3 = lean_unsigned_to_nat(105u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_Lean_mkConst(x_2, x_9);
x_11 = l_Lean_Meta_Lean_Meta_Basic___instance__5___closed__1;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Lean_Meta_Basic___instance__11___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_1);
x_16 = l_Lean_ParserCompiler_compileParserBody___rarg(x_1, x_10, x_4, x_15, x_13, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_13, x_18);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_mk_syntax_ident(x_2);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = l_Lean_nullKind;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
if (x_3 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = 1;
x_31 = l_Lean_addAttribute(x_21, x_29, x_26, x_30, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_31) == 0)
{
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = 1;
x_42 = l_Lean_addAttribute(x_21, x_40, x_26, x_41, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_42) == 0)
{
return x_42;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_dec(x_19);
x_50 = l_Lean_ParserCompiler_compileParser___rarg___closed__2;
x_51 = l_Lean_ParserCompiler_compileParser___rarg___closed__5;
x_52 = lean_panic_fn(x_50, x_51);
x_53 = lean_apply_4(x_52, x_5, x_6, x_7, x_49);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_16, 0);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParser___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_ParserCompiler_interpretParser_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_interpretParser_match__1___rarg), 3, 0);
return x_3;
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
lean_object* l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_eval_const(x_9, x_10, x_1);
lean_dec(x_9);
x_12 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_11, x_2, x_3, x_4, x_8);
lean_dec(x_11);
return x_12;
}
}
lean_object* l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
x_17 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_free_object(x_11);
x_21 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_2, x_4, x_5, x_6, x_14);
lean_dec(x_2);
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
x_25 = lean_apply_5(x_24, x_22, x_4, x_5, x_6, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_31 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_30, x_15, x_2);
lean_dec(x_15);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_free_object(x_11);
x_32 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_32, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Name_append(x_2, x_35);
lean_dec(x_2);
x_37 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_36, x_4, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
lean_ctor_set(x_11, 0, x_42);
return x_11;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_16);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_43, x_15, x_2);
lean_dec(x_15);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; lean_object* x_46; 
lean_free_object(x_11);
x_45 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_45, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_Lean_Name_append(x_2, x_48);
lean_dec(x_2);
x_50 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_49, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_49);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
lean_dec(x_44);
lean_ctor_set(x_11, 0, x_55);
return x_11;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
x_60 = l_Lean_ParserCompiler_compileParserBody___rarg___closed__3;
x_61 = l_Lean_Expr_isConstOf(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1;
x_63 = l_Lean_Expr_isConstOf(x_59, x_62);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_2, x_4, x_5, x_6, x_57);
lean_dec(x_2);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_apply_5(x_67, x_65, x_4, x_5, x_6, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_73, x_58, x_2);
lean_dec(x_58);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; lean_object* x_76; 
x_75 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_75, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
lean_dec(x_1);
x_79 = l_Lean_Name_append(x_2, x_78);
lean_dec(x_2);
x_80 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_79, x_4, x_5, x_6, x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_57);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_59);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_87, x_58, x_2);
lean_dec(x_58);
lean_dec(x_87);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; lean_object* x_90; 
x_89 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_89, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
lean_dec(x_1);
x_93 = l_Lean_Name_append(x_2, x_92);
lean_dec(x_2);
x_94 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_93, x_4, x_5, x_6, x_91);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_88, 0);
lean_inc(x_99);
lean_dec(x_88);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_57);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_8);
if (x_101 == 0)
{
return x_8;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_8, 0);
x_103 = lean_ctor_get(x_8, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_8);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_interpretParser___rarg___boxed), 7, 0);
return x_2;
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
lean_object* l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_evalConst___at_Lean_ParserCompiler_interpretParser___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_ParserCompiler_interpretParser___rarg(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
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
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_ParserCompiler_interpretParser___rarg(x_1, x_3, x_9, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1), 3, 2);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_11);
x_20 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_18, x_16, x_19);
lean_dec(x_18);
x_21 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(x_20, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
x_27 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_4, x_26, x_5, x_6, x_7, x_8);
return x_27;
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
l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1 = _init_l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_preprocessParserBody___rarg___lambda__1___closed__1);
l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1 = _init_l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1();
lean_mark_persistent(l_Array_iterateM_u2082Aux___at_Lean_ParserCompiler_compileParserBody___spec__4___rarg___closed__1);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__1 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__1);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__2 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__2);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__3 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__3);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__4 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__4();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__4);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__5 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__5();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__5);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__6 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__6();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__6);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__7 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__7();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__7);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__8 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__8();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__8);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__9 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__9();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__9);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__10 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__10();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__10);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__11 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__11();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__11);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__12 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__12();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__12);
l_Lean_ParserCompiler_compileParserBody___rarg___closed__13 = _init_l_Lean_ParserCompiler_compileParserBody___rarg___closed__13();
lean_mark_persistent(l_Lean_ParserCompiler_compileParserBody___rarg___closed__13);
l_Lean_ParserCompiler_compileParser___rarg___closed__1 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__1);
l_Lean_ParserCompiler_compileParser___rarg___closed__2 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__2);
l_Lean_ParserCompiler_compileParser___rarg___closed__3 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__3);
l_Lean_ParserCompiler_compileParser___rarg___closed__4 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__4();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__4);
l_Lean_ParserCompiler_compileParser___rarg___closed__5 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__5();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
