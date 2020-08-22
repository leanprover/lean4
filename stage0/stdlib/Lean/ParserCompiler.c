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
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isReducible___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_Table_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object*);
lean_object* lean_add_attribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_mkInitAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Core_checkRecDepth___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_inhabited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l_Lean_Meta_inferType(x_19, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_24, x_2, x_8, x_9, x_10, x_11, x_25);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType(x_17, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_Meta_inferType(x_18, x_7, x_8, x_9, x_10, x_11);
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
x_26 = l_Lean_Meta_forallTelescope___rarg(x_23, x_25, x_7, x_8, x_9, x_10, x_24);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed), 11, 0);
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
x_12 = l_Lean_Meta_mkLambda(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
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
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(x_1, x_2, x_5, x_5, x_3, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(x_1, x_4, x_4, x_2, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
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
x_8 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_30 = l_Lean_Meta_isReducible___closed__2;
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = lean_apply_5(x_31, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_36, x_33, x_22);
lean_dec(x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_inc(x_35);
x_38 = l_Lean_Name_append___main(x_22, x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_39 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_22, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_ConstantInfo_type(x_40);
x_43 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_44 = l_Lean_Meta_forallTelescope___rarg(x_42, x_43, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_128; uint8_t x_129; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_128 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_129 = l_Lean_Expr_isConstOf(x_45, x_128);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_131 = l_Lean_Expr_isConstOf(x_45, x_130);
lean_dec(x_45);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_132 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_1);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_135, 0, x_35);
x_136 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_141 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_145 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_145, x_3, x_4, x_5, x_6, x_134);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_35);
lean_dec(x_9);
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
lean_dec(x_132);
x_148 = lean_ctor_get(x_133, 0);
lean_inc(x_148);
lean_dec(x_133);
x_2 = x_148;
x_7 = x_147;
goto _start;
}
}
else
{
uint8_t x_150; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_132);
if (x_150 == 0)
{
return x_132;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_132, 0);
x_152 = lean_ctor_get(x_132, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_132);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
x_154 = lean_box(0);
x_47 = x_154;
goto block_127;
}
}
else
{
lean_object* x_155; 
lean_dec(x_45);
x_155 = lean_box(0);
x_47 = x_155;
goto block_127;
}
block_127:
{
lean_object* x_48; 
lean_dec(x_47);
x_48 = l_Lean_ConstantInfo_value_x3f(x_40);
lean_dec(x_40);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_1);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_35);
x_50 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_59, x_3, x_4, x_5, x_6, x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_35);
lean_dec(x_9);
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_63 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_62, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_87 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_88 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed), 9, 2);
lean_closure_set(x_88, 0, x_1);
lean_closure_set(x_88, 1, x_87);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_89 = l_Lean_Meta_forallTelescope___rarg(x_42, x_88, x_3, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_box(0);
lean_inc(x_38);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_38);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_90);
x_94 = lean_box(0);
x_95 = 0;
x_96 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_64);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*3, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_98 = lean_apply_5(x_31, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Options_empty;
x_102 = l_Lean_Environment_addAndCompile(x_99, x_101, x_97);
lean_dec(x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_KernelException_toMessageData(x_103, x_101);
x_105 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_104);
x_106 = l_Lean_Format_pretty(x_105, x_101);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_108, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_102, 0);
lean_inc(x_114);
lean_dec(x_102);
x_66 = x_114;
x_67 = x_100;
goto block_86;
}
}
else
{
uint8_t x_115; 
lean_dec(x_97);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_98);
if (x_115 == 0)
{
return x_98;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_98, 0);
x_117 = lean_ctor_get(x_98, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_98);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_64);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_89);
if (x_119 == 0)
{
return x_89;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_89, 0);
x_121 = lean_ctor_get(x_89, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_89);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
block_86:
{
lean_object* x_68; lean_object* x_69; 
lean_inc(x_38);
x_68 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_36, x_66, x_22, x_38);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_68, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = l_Lean_mkConst(x_38, x_71);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_72);
x_73 = l_Lean_Meta_inferType(x_72, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed), 11, 4);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_43);
lean_closure_set(x_76, 2, x_29);
lean_closure_set(x_76, 3, x_72);
x_77 = l_Lean_Meta_forallTelescope___rarg(x_74, x_76, x_3, x_4, x_5, x_6, x_75);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_72);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_69);
if (x_82 == 0)
{
return x_69;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_69, 0);
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_69);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_63);
if (x_123 == 0)
{
return x_63;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_63, 0);
x_125 = lean_ctor_get(x_63, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_63);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_44);
if (x_156 == 0)
{
return x_44;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_44, 0);
x_158 = lean_ctor_get(x_44, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_44);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_39);
if (x_160 == 0)
{
return x_39;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_39, 0);
x_162 = lean_ctor_get(x_39, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_39);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_9);
x_164 = lean_ctor_get(x_37, 0);
lean_inc(x_164);
lean_dec(x_37);
x_165 = lean_box(0);
x_166 = l_Lean_mkConst(x_164, x_165);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_166);
x_167 = l_Lean_Meta_inferType(x_166, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed), 10, 3);
lean_closure_set(x_170, 0, x_1);
lean_closure_set(x_170, 1, x_29);
lean_closure_set(x_170, 2, x_166);
x_171 = l_Lean_Meta_forallTelescope___rarg(x_168, x_170, x_3, x_4, x_5, x_6, x_169);
return x_171;
}
else
{
uint8_t x_172; 
lean_dec(x_166);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_167);
if (x_172 == 0)
{
return x_167;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_167, 0);
x_174 = lean_ctor_get(x_167, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_167);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_32);
if (x_176 == 0)
{
return x_32;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_32, 0);
x_178 = lean_ctor_get(x_32, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_32);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_11);
lean_dec(x_1);
x_180 = lean_box(0);
x_12 = x_180;
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
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_19 = lean_alloc_ctor(9, 2, 0);
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
uint8_t x_181; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_8);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_8, 0);
lean_dec(x_182);
return x_8;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_8, 1);
lean_inc(x_183);
lean_dec(x_8);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_9);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
case 2:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_8, 1);
lean_inc(x_185);
lean_dec(x_8);
x_186 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_186) == 4)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_197 = lean_ctor_get(x_186, 0);
lean_inc(x_197);
lean_dec(x_186);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_198);
x_200 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_199);
x_201 = lean_mk_array(x_199, x_200);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_sub(x_199, x_202);
lean_dec(x_199);
lean_inc(x_9);
x_204 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_201, x_203);
x_205 = l_Lean_Meta_isReducible___closed__2;
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_inc(x_206);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_207 = lean_apply_5(x_206, x_3, x_4, x_5, x_6, x_185);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_1, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_1, 2);
lean_inc(x_211);
x_212 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_211, x_208, x_197);
lean_dec(x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_inc(x_210);
x_213 = l_Lean_Name_append___main(x_197, x_210);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_197);
x_214 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_197, x_3, x_4, x_5, x_6, x_209);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_ConstantInfo_type(x_215);
x_218 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_217);
x_219 = l_Lean_Meta_forallTelescope___rarg(x_217, x_218, x_3, x_4, x_5, x_6, x_216);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_303; uint8_t x_304; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_303 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_304 = l_Lean_Expr_isConstOf(x_220, x_303);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_306 = l_Lean_Expr_isConstOf(x_220, x_305);
lean_dec(x_220);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_307 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_1);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_310, 0, x_210);
x_311 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_312 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
x_313 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_316 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_318, 0, x_314);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_320 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_320, x_3, x_4, x_5, x_6, x_309);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_210);
lean_dec(x_9);
x_322 = lean_ctor_get(x_307, 1);
lean_inc(x_322);
lean_dec(x_307);
x_323 = lean_ctor_get(x_308, 0);
lean_inc(x_323);
lean_dec(x_308);
x_2 = x_323;
x_7 = x_322;
goto _start;
}
}
else
{
uint8_t x_325; 
lean_dec(x_210);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_307);
if (x_325 == 0)
{
return x_307;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_307, 0);
x_327 = lean_ctor_get(x_307, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_307);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
lean_object* x_329; 
x_329 = lean_box(0);
x_222 = x_329;
goto block_302;
}
}
else
{
lean_object* x_330; 
lean_dec(x_220);
x_330 = lean_box(0);
x_222 = x_330;
goto block_302;
}
block_302:
{
lean_object* x_223; 
lean_dec(x_222);
x_223 = l_Lean_ConstantInfo_value_x3f(x_215);
lean_dec(x_215);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_1);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_210);
x_225 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_226 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_234 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_234, x_3, x_4, x_5, x_6, x_221);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_210);
lean_dec(x_9);
x_236 = lean_ctor_get(x_223, 0);
lean_inc(x_236);
lean_dec(x_223);
x_237 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_236);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_238 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_237, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_262 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_263 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed), 9, 2);
lean_closure_set(x_263, 0, x_1);
lean_closure_set(x_263, 1, x_262);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_264 = l_Lean_Meta_forallTelescope___rarg(x_217, x_263, x_3, x_4, x_5, x_6, x_240);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_box(0);
lean_inc(x_213);
x_268 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_268, 0, x_213);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_268, 2, x_265);
x_269 = lean_box(0);
x_270 = 0;
x_271 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_239);
lean_ctor_set(x_271, 2, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*3, x_270);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_271);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_273 = lean_apply_5(x_206, x_3, x_4, x_5, x_6, x_266);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_Options_empty;
x_277 = l_Lean_Environment_addAndCompile(x_274, x_276, x_272);
lean_dec(x_272);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_1);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec(x_277);
x_279 = l_Lean_KernelException_toMessageData(x_278, x_276);
x_280 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_279);
x_281 = l_Lean_Format_pretty(x_280, x_276);
x_282 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_282, 0, x_281);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_282);
x_284 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_283, x_3, x_4, x_5, x_6, x_275);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
return x_284;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_284);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
else
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_277, 0);
lean_inc(x_289);
lean_dec(x_277);
x_241 = x_289;
x_242 = x_275;
goto block_261;
}
}
else
{
uint8_t x_290; 
lean_dec(x_272);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_273);
if (x_290 == 0)
{
return x_273;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_273, 0);
x_292 = lean_ctor_get(x_273, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_273);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_239);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_264);
if (x_294 == 0)
{
return x_264;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_264, 0);
x_296 = lean_ctor_get(x_264, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_264);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
block_261:
{
lean_object* x_243; lean_object* x_244; 
lean_inc(x_213);
x_243 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_211, x_241, x_197, x_213);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_244 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_243, x_3, x_4, x_5, x_6, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_246 = lean_box(0);
x_247 = l_Lean_mkConst(x_213, x_246);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_247);
x_248 = l_Lean_Meta_inferType(x_247, x_3, x_4, x_5, x_6, x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed), 11, 4);
lean_closure_set(x_251, 0, x_1);
lean_closure_set(x_251, 1, x_218);
lean_closure_set(x_251, 2, x_204);
lean_closure_set(x_251, 3, x_247);
x_252 = l_Lean_Meta_forallTelescope___rarg(x_249, x_251, x_3, x_4, x_5, x_6, x_250);
return x_252;
}
else
{
uint8_t x_253; 
lean_dec(x_247);
lean_dec(x_204);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_253 = !lean_is_exclusive(x_248);
if (x_253 == 0)
{
return x_248;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_248, 0);
x_255 = lean_ctor_get(x_248, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_248);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_213);
lean_dec(x_204);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_244);
if (x_257 == 0)
{
return x_244;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_244, 0);
x_259 = lean_ctor_get(x_244, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_244);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_238);
if (x_298 == 0)
{
return x_238;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_238, 0);
x_300 = lean_ctor_get(x_238, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_238);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_219);
if (x_331 == 0)
{
return x_219;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_219, 0);
x_333 = lean_ctor_get(x_219, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_219);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
uint8_t x_335; 
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_214);
if (x_335 == 0)
{
return x_214;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_214, 0);
x_337 = lean_ctor_get(x_214, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_214);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_206);
lean_dec(x_197);
lean_dec(x_9);
x_339 = lean_ctor_get(x_212, 0);
lean_inc(x_339);
lean_dec(x_212);
x_340 = lean_box(0);
x_341 = l_Lean_mkConst(x_339, x_340);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_341);
x_342 = l_Lean_Meta_inferType(x_341, x_3, x_4, x_5, x_6, x_209);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed), 10, 3);
lean_closure_set(x_345, 0, x_1);
lean_closure_set(x_345, 1, x_204);
lean_closure_set(x_345, 2, x_341);
x_346 = l_Lean_Meta_forallTelescope___rarg(x_343, x_345, x_3, x_4, x_5, x_6, x_344);
return x_346;
}
else
{
uint8_t x_347; 
lean_dec(x_341);
lean_dec(x_204);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_347 = !lean_is_exclusive(x_342);
if (x_347 == 0)
{
return x_342;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_342, 0);
x_349 = lean_ctor_get(x_342, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_342);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_207);
if (x_351 == 0)
{
return x_207;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_207, 0);
x_353 = lean_ctor_get(x_207, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_207);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
lean_object* x_355; 
lean_dec(x_186);
lean_dec(x_1);
x_355 = lean_box(0);
x_187 = x_355;
goto block_196;
}
block_196:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_187);
x_188 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_192 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_194, x_3, x_4, x_5, x_6, x_185);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_195;
}
}
case 3:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_8, 1);
lean_inc(x_356);
lean_dec(x_8);
x_357 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_357) == 4)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_368 = lean_ctor_get(x_357, 0);
lean_inc(x_368);
lean_dec(x_357);
x_369 = lean_unsigned_to_nat(0u);
x_370 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_369);
x_371 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_370);
x_372 = lean_mk_array(x_370, x_371);
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_nat_sub(x_370, x_373);
lean_dec(x_370);
lean_inc(x_9);
x_375 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_372, x_374);
x_376 = l_Lean_Meta_isReducible___closed__2;
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_inc(x_377);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_378 = lean_apply_5(x_377, x_3, x_4, x_5, x_6, x_356);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_ctor_get(x_1, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_1, 2);
lean_inc(x_382);
x_383 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_382, x_379, x_368);
lean_dec(x_379);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_inc(x_381);
x_384 = l_Lean_Name_append___main(x_368, x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_368);
x_385 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_368, x_3, x_4, x_5, x_6, x_380);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Lean_ConstantInfo_type(x_386);
x_389 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_388);
x_390 = l_Lean_Meta_forallTelescope___rarg(x_388, x_389, x_3, x_4, x_5, x_6, x_387);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_474; uint8_t x_475; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_474 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_475 = l_Lean_Expr_isConstOf(x_391, x_474);
if (x_475 == 0)
{
lean_object* x_476; uint8_t x_477; 
x_476 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_477 = l_Lean_Expr_isConstOf(x_391, x_476);
lean_dec(x_391);
if (x_477 == 0)
{
lean_object* x_478; 
lean_dec(x_388);
lean_dec(x_386);
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_478 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_392);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_1);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_481 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_481, 0, x_381);
x_482 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_483 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_481);
x_484 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_485 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
x_486 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_487 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_488, 0, x_487);
x_489 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_491 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_491, x_3, x_4, x_5, x_6, x_480);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; 
lean_dec(x_381);
lean_dec(x_9);
x_493 = lean_ctor_get(x_478, 1);
lean_inc(x_493);
lean_dec(x_478);
x_494 = lean_ctor_get(x_479, 0);
lean_inc(x_494);
lean_dec(x_479);
x_2 = x_494;
x_7 = x_493;
goto _start;
}
}
else
{
uint8_t x_496; 
lean_dec(x_381);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_496 = !lean_is_exclusive(x_478);
if (x_496 == 0)
{
return x_478;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_478, 0);
x_498 = lean_ctor_get(x_478, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_478);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
}
else
{
lean_object* x_500; 
x_500 = lean_box(0);
x_393 = x_500;
goto block_473;
}
}
else
{
lean_object* x_501; 
lean_dec(x_391);
x_501 = lean_box(0);
x_393 = x_501;
goto block_473;
}
block_473:
{
lean_object* x_394; 
lean_dec(x_393);
x_394 = l_Lean_ConstantInfo_value_x3f(x_386);
lean_dec(x_386);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_388);
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_1);
x_395 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_395, 0, x_381);
x_396 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_397 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_395);
x_398 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_399 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_401 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_402, 0, x_401);
x_403 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_403, 0, x_399);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_405 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
x_406 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_405, x_3, x_4, x_5, x_6, x_392);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_381);
lean_dec(x_9);
x_407 = lean_ctor_get(x_394, 0);
lean_inc(x_407);
lean_dec(x_394);
x_408 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_407);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_409 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_408, x_3, x_4, x_5, x_6, x_392);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_433 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_434 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed), 9, 2);
lean_closure_set(x_434, 0, x_1);
lean_closure_set(x_434, 1, x_433);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_435 = l_Lean_Meta_forallTelescope___rarg(x_388, x_434, x_3, x_4, x_5, x_6, x_411);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_box(0);
lean_inc(x_384);
x_439 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_439, 0, x_384);
lean_ctor_set(x_439, 1, x_438);
lean_ctor_set(x_439, 2, x_436);
x_440 = lean_box(0);
x_441 = 0;
x_442 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_410);
lean_ctor_set(x_442, 2, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*3, x_441);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_442);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_444 = lean_apply_5(x_377, x_3, x_4, x_5, x_6, x_437);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = l_Lean_Options_empty;
x_448 = l_Lean_Environment_addAndCompile(x_445, x_447, x_443);
lean_dec(x_443);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; 
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_1);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec(x_448);
x_450 = l_Lean_KernelException_toMessageData(x_449, x_447);
x_451 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_450);
x_452 = l_Lean_Format_pretty(x_451, x_447);
x_453 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_453, 0, x_452);
x_454 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_454, 0, x_453);
x_455 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_454, x_3, x_4, x_5, x_6, x_446);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_456 = !lean_is_exclusive(x_455);
if (x_456 == 0)
{
return x_455;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_455, 0);
x_458 = lean_ctor_get(x_455, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_455);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
else
{
lean_object* x_460; 
x_460 = lean_ctor_get(x_448, 0);
lean_inc(x_460);
lean_dec(x_448);
x_412 = x_460;
x_413 = x_446;
goto block_432;
}
}
else
{
uint8_t x_461; 
lean_dec(x_443);
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_444);
if (x_461 == 0)
{
return x_444;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_444, 0);
x_463 = lean_ctor_get(x_444, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_444);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
else
{
uint8_t x_465; 
lean_dec(x_410);
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_465 = !lean_is_exclusive(x_435);
if (x_465 == 0)
{
return x_435;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_435, 0);
x_467 = lean_ctor_get(x_435, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_435);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
block_432:
{
lean_object* x_414; lean_object* x_415; 
lean_inc(x_384);
x_414 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_382, x_412, x_368, x_384);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_415 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_414, x_3, x_4, x_5, x_6, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
lean_dec(x_415);
x_417 = lean_box(0);
x_418 = l_Lean_mkConst(x_384, x_417);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_418);
x_419 = l_Lean_Meta_inferType(x_418, x_3, x_4, x_5, x_6, x_416);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed), 11, 4);
lean_closure_set(x_422, 0, x_1);
lean_closure_set(x_422, 1, x_389);
lean_closure_set(x_422, 2, x_375);
lean_closure_set(x_422, 3, x_418);
x_423 = l_Lean_Meta_forallTelescope___rarg(x_420, x_422, x_3, x_4, x_5, x_6, x_421);
return x_423;
}
else
{
uint8_t x_424; 
lean_dec(x_418);
lean_dec(x_375);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_424 = !lean_is_exclusive(x_419);
if (x_424 == 0)
{
return x_419;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_419, 0);
x_426 = lean_ctor_get(x_419, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_419);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
else
{
uint8_t x_428; 
lean_dec(x_384);
lean_dec(x_375);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_428 = !lean_is_exclusive(x_415);
if (x_428 == 0)
{
return x_415;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_415, 0);
x_430 = lean_ctor_get(x_415, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_415);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_388);
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_469 = !lean_is_exclusive(x_409);
if (x_469 == 0)
{
return x_409;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_409, 0);
x_471 = lean_ctor_get(x_409, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_409);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_388);
lean_dec(x_386);
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_390);
if (x_502 == 0)
{
return x_390;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_390, 0);
x_504 = lean_ctor_get(x_390, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_390);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_385);
if (x_506 == 0)
{
return x_385;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_385, 0);
x_508 = lean_ctor_get(x_385, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_385);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_368);
lean_dec(x_9);
x_510 = lean_ctor_get(x_383, 0);
lean_inc(x_510);
lean_dec(x_383);
x_511 = lean_box(0);
x_512 = l_Lean_mkConst(x_510, x_511);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_512);
x_513 = l_Lean_Meta_inferType(x_512, x_3, x_4, x_5, x_6, x_380);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed), 10, 3);
lean_closure_set(x_516, 0, x_1);
lean_closure_set(x_516, 1, x_375);
lean_closure_set(x_516, 2, x_512);
x_517 = l_Lean_Meta_forallTelescope___rarg(x_514, x_516, x_3, x_4, x_5, x_6, x_515);
return x_517;
}
else
{
uint8_t x_518; 
lean_dec(x_512);
lean_dec(x_375);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_518 = !lean_is_exclusive(x_513);
if (x_518 == 0)
{
return x_513;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_513, 0);
x_520 = lean_ctor_get(x_513, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_513);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
}
else
{
uint8_t x_522; 
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_522 = !lean_is_exclusive(x_378);
if (x_522 == 0)
{
return x_378;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_378, 0);
x_524 = lean_ctor_get(x_378, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_378);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
else
{
lean_object* x_526; 
lean_dec(x_357);
lean_dec(x_1);
x_526 = lean_box(0);
x_358 = x_526;
goto block_367;
}
block_367:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_358);
x_359 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_360 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_360, 0, x_359);
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_360);
x_362 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_363 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_365 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_365, x_3, x_4, x_5, x_6, x_356);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_366;
}
}
case 4:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_8, 1);
lean_inc(x_527);
lean_dec(x_8);
x_528 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_528) == 4)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_539 = lean_ctor_get(x_528, 0);
lean_inc(x_539);
lean_dec(x_528);
x_540 = lean_unsigned_to_nat(0u);
x_541 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_540);
x_542 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_541);
x_543 = lean_mk_array(x_541, x_542);
x_544 = lean_unsigned_to_nat(1u);
x_545 = lean_nat_sub(x_541, x_544);
lean_dec(x_541);
lean_inc(x_9);
x_546 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_543, x_545);
x_547 = l_Lean_Meta_isReducible___closed__2;
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
lean_inc(x_548);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_549 = lean_apply_5(x_548, x_3, x_4, x_5, x_6, x_527);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = lean_ctor_get(x_1, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_1, 2);
lean_inc(x_553);
x_554 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_553, x_550, x_539);
lean_dec(x_550);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; 
lean_inc(x_552);
x_555 = l_Lean_Name_append___main(x_539, x_552);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_539);
x_556 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_539, x_3, x_4, x_5, x_6, x_551);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = l_Lean_ConstantInfo_type(x_557);
x_560 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_559);
x_561 = l_Lean_Meta_forallTelescope___rarg(x_559, x_560, x_3, x_4, x_5, x_6, x_558);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_645; uint8_t x_646; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_645 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_646 = l_Lean_Expr_isConstOf(x_562, x_645);
if (x_646 == 0)
{
lean_object* x_647; uint8_t x_648; 
x_647 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_648 = l_Lean_Expr_isConstOf(x_562, x_647);
lean_dec(x_562);
if (x_648 == 0)
{
lean_object* x_649; 
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_649 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_563);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_1);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_652 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_652, 0, x_552);
x_653 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_654 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_652);
x_655 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_656 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
x_657 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_658 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_658, 0, x_657);
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
x_660 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_660, 0, x_656);
lean_ctor_set(x_660, 1, x_659);
x_661 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_662 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_662, 0, x_660);
lean_ctor_set(x_662, 1, x_661);
x_663 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_662, x_3, x_4, x_5, x_6, x_651);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_663;
}
else
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_552);
lean_dec(x_9);
x_664 = lean_ctor_get(x_649, 1);
lean_inc(x_664);
lean_dec(x_649);
x_665 = lean_ctor_get(x_650, 0);
lean_inc(x_665);
lean_dec(x_650);
x_2 = x_665;
x_7 = x_664;
goto _start;
}
}
else
{
uint8_t x_667; 
lean_dec(x_552);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_667 = !lean_is_exclusive(x_649);
if (x_667 == 0)
{
return x_649;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_668 = lean_ctor_get(x_649, 0);
x_669 = lean_ctor_get(x_649, 1);
lean_inc(x_669);
lean_inc(x_668);
lean_dec(x_649);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_668);
lean_ctor_set(x_670, 1, x_669);
return x_670;
}
}
}
else
{
lean_object* x_671; 
x_671 = lean_box(0);
x_564 = x_671;
goto block_644;
}
}
else
{
lean_object* x_672; 
lean_dec(x_562);
x_672 = lean_box(0);
x_564 = x_672;
goto block_644;
}
block_644:
{
lean_object* x_565; 
lean_dec(x_564);
x_565 = l_Lean_ConstantInfo_value_x3f(x_557);
lean_dec(x_557);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_559);
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_1);
x_566 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_566, 0, x_552);
x_567 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_568 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_566);
x_569 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_570 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_572 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_572, 0, x_571);
x_573 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_573, 0, x_572);
x_574 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_574, 0, x_570);
lean_ctor_set(x_574, 1, x_573);
x_575 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_576 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set(x_576, 1, x_575);
x_577 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_576, x_3, x_4, x_5, x_6, x_563);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_552);
lean_dec(x_9);
x_578 = lean_ctor_get(x_565, 0);
lean_inc(x_578);
lean_dec(x_565);
x_579 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_578);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_580 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_579, x_3, x_4, x_5, x_6, x_563);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_604 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_605 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed), 9, 2);
lean_closure_set(x_605, 0, x_1);
lean_closure_set(x_605, 1, x_604);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_606 = l_Lean_Meta_forallTelescope___rarg(x_559, x_605, x_3, x_4, x_5, x_6, x_582);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_box(0);
lean_inc(x_555);
x_610 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_610, 0, x_555);
lean_ctor_set(x_610, 1, x_609);
lean_ctor_set(x_610, 2, x_607);
x_611 = lean_box(0);
x_612 = 0;
x_613 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_581);
lean_ctor_set(x_613, 2, x_611);
lean_ctor_set_uint8(x_613, sizeof(void*)*3, x_612);
x_614 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_614, 0, x_613);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_615 = lean_apply_5(x_548, x_3, x_4, x_5, x_6, x_608);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_618 = l_Lean_Options_empty;
x_619 = l_Lean_Environment_addAndCompile(x_616, x_618, x_614);
lean_dec(x_614);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_1);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
lean_dec(x_619);
x_621 = l_Lean_KernelException_toMessageData(x_620, x_618);
x_622 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_621);
x_623 = l_Lean_Format_pretty(x_622, x_618);
x_624 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_624, 0, x_623);
x_625 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_625, 0, x_624);
x_626 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_625, x_3, x_4, x_5, x_6, x_617);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
return x_626;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_626);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
else
{
lean_object* x_631; 
x_631 = lean_ctor_get(x_619, 0);
lean_inc(x_631);
lean_dec(x_619);
x_583 = x_631;
x_584 = x_617;
goto block_603;
}
}
else
{
uint8_t x_632; 
lean_dec(x_614);
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_632 = !lean_is_exclusive(x_615);
if (x_632 == 0)
{
return x_615;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_615, 0);
x_634 = lean_ctor_get(x_615, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_615);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
else
{
uint8_t x_636; 
lean_dec(x_581);
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_636 = !lean_is_exclusive(x_606);
if (x_636 == 0)
{
return x_606;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_606, 0);
x_638 = lean_ctor_get(x_606, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_606);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
block_603:
{
lean_object* x_585; lean_object* x_586; 
lean_inc(x_555);
x_585 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_553, x_583, x_539, x_555);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_586 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_585, x_3, x_4, x_5, x_6, x_584);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
x_588 = lean_box(0);
x_589 = l_Lean_mkConst(x_555, x_588);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_589);
x_590 = l_Lean_Meta_inferType(x_589, x_3, x_4, x_5, x_6, x_587);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed), 11, 4);
lean_closure_set(x_593, 0, x_1);
lean_closure_set(x_593, 1, x_560);
lean_closure_set(x_593, 2, x_546);
lean_closure_set(x_593, 3, x_589);
x_594 = l_Lean_Meta_forallTelescope___rarg(x_591, x_593, x_3, x_4, x_5, x_6, x_592);
return x_594;
}
else
{
uint8_t x_595; 
lean_dec(x_589);
lean_dec(x_546);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_595 = !lean_is_exclusive(x_590);
if (x_595 == 0)
{
return x_590;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_590, 0);
x_597 = lean_ctor_get(x_590, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_590);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
else
{
uint8_t x_599; 
lean_dec(x_555);
lean_dec(x_546);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_586);
if (x_599 == 0)
{
return x_586;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_586, 0);
x_601 = lean_ctor_get(x_586, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_586);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
}
else
{
uint8_t x_640; 
lean_dec(x_559);
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_640 = !lean_is_exclusive(x_580);
if (x_640 == 0)
{
return x_580;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_580, 0);
x_642 = lean_ctor_get(x_580, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_580);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
}
}
else
{
uint8_t x_673; 
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_673 = !lean_is_exclusive(x_561);
if (x_673 == 0)
{
return x_561;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_674 = lean_ctor_get(x_561, 0);
x_675 = lean_ctor_get(x_561, 1);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_561);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_674);
lean_ctor_set(x_676, 1, x_675);
return x_676;
}
}
}
else
{
uint8_t x_677; 
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_677 = !lean_is_exclusive(x_556);
if (x_677 == 0)
{
return x_556;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_556, 0);
x_679 = lean_ctor_get(x_556, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_556);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_678);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_548);
lean_dec(x_539);
lean_dec(x_9);
x_681 = lean_ctor_get(x_554, 0);
lean_inc(x_681);
lean_dec(x_554);
x_682 = lean_box(0);
x_683 = l_Lean_mkConst(x_681, x_682);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_683);
x_684 = l_Lean_Meta_inferType(x_683, x_3, x_4, x_5, x_6, x_551);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed), 10, 3);
lean_closure_set(x_687, 0, x_1);
lean_closure_set(x_687, 1, x_546);
lean_closure_set(x_687, 2, x_683);
x_688 = l_Lean_Meta_forallTelescope___rarg(x_685, x_687, x_3, x_4, x_5, x_6, x_686);
return x_688;
}
else
{
uint8_t x_689; 
lean_dec(x_683);
lean_dec(x_546);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_689 = !lean_is_exclusive(x_684);
if (x_689 == 0)
{
return x_684;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_690 = lean_ctor_get(x_684, 0);
x_691 = lean_ctor_get(x_684, 1);
lean_inc(x_691);
lean_inc(x_690);
lean_dec(x_684);
x_692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_692, 0, x_690);
lean_ctor_set(x_692, 1, x_691);
return x_692;
}
}
}
}
else
{
uint8_t x_693; 
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_693 = !lean_is_exclusive(x_549);
if (x_693 == 0)
{
return x_549;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_549, 0);
x_695 = lean_ctor_get(x_549, 1);
lean_inc(x_695);
lean_inc(x_694);
lean_dec(x_549);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
return x_696;
}
}
}
else
{
lean_object* x_697; 
lean_dec(x_528);
lean_dec(x_1);
x_697 = lean_box(0);
x_529 = x_697;
goto block_538;
}
block_538:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_529);
x_530 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_531 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_531, 0, x_530);
x_532 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_532, 0, x_531);
x_533 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_534 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_532);
x_535 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_536 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
x_537 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_536, x_3, x_4, x_5, x_6, x_527);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_537;
}
}
case 5:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_698 = lean_ctor_get(x_8, 1);
lean_inc(x_698);
lean_dec(x_8);
x_699 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_699) == 4)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_710 = lean_ctor_get(x_699, 0);
lean_inc(x_710);
lean_dec(x_699);
x_711 = lean_unsigned_to_nat(0u);
x_712 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_711);
x_713 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_712);
x_714 = lean_mk_array(x_712, x_713);
x_715 = lean_unsigned_to_nat(1u);
x_716 = lean_nat_sub(x_712, x_715);
lean_dec(x_712);
lean_inc(x_9);
x_717 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_714, x_716);
x_718 = l_Lean_Meta_isReducible___closed__2;
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
lean_inc(x_719);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_720 = lean_apply_5(x_719, x_3, x_4, x_5, x_6, x_698);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
x_723 = lean_ctor_get(x_1, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_1, 2);
lean_inc(x_724);
x_725 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_724, x_721, x_710);
lean_dec(x_721);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; 
lean_inc(x_723);
x_726 = l_Lean_Name_append___main(x_710, x_723);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_710);
x_727 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_710, x_3, x_4, x_5, x_6, x_722);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_730 = l_Lean_ConstantInfo_type(x_728);
x_731 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_730);
x_732 = l_Lean_Meta_forallTelescope___rarg(x_730, x_731, x_3, x_4, x_5, x_6, x_729);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_816; uint8_t x_817; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_816 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_817 = l_Lean_Expr_isConstOf(x_733, x_816);
if (x_817 == 0)
{
lean_object* x_818; uint8_t x_819; 
x_818 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_819 = l_Lean_Expr_isConstOf(x_733, x_818);
lean_dec(x_733);
if (x_819 == 0)
{
lean_object* x_820; 
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_820 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_734);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_1);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
x_823 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_823, 0, x_723);
x_824 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_825 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
x_826 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_827 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_826);
x_828 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_829 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_829, 0, x_828);
x_830 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_830, 0, x_829);
x_831 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_831, 0, x_827);
lean_ctor_set(x_831, 1, x_830);
x_832 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_833 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_833, 0, x_831);
lean_ctor_set(x_833, 1, x_832);
x_834 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_833, x_3, x_4, x_5, x_6, x_822);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_834;
}
else
{
lean_object* x_835; lean_object* x_836; 
lean_dec(x_723);
lean_dec(x_9);
x_835 = lean_ctor_get(x_820, 1);
lean_inc(x_835);
lean_dec(x_820);
x_836 = lean_ctor_get(x_821, 0);
lean_inc(x_836);
lean_dec(x_821);
x_2 = x_836;
x_7 = x_835;
goto _start;
}
}
else
{
uint8_t x_838; 
lean_dec(x_723);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_838 = !lean_is_exclusive(x_820);
if (x_838 == 0)
{
return x_820;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_820, 0);
x_840 = lean_ctor_get(x_820, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_820);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
else
{
lean_object* x_842; 
x_842 = lean_box(0);
x_735 = x_842;
goto block_815;
}
}
else
{
lean_object* x_843; 
lean_dec(x_733);
x_843 = lean_box(0);
x_735 = x_843;
goto block_815;
}
block_815:
{
lean_object* x_736; 
lean_dec(x_735);
x_736 = l_Lean_ConstantInfo_value_x3f(x_728);
lean_dec(x_728);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_730);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_1);
x_737 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_737, 0, x_723);
x_738 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_739 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_737);
x_740 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_741 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_741, 0, x_739);
lean_ctor_set(x_741, 1, x_740);
x_742 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_743 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_743, 0, x_742);
x_744 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_744, 0, x_743);
x_745 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_745, 0, x_741);
lean_ctor_set(x_745, 1, x_744);
x_746 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_747 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
x_748 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_747, x_3, x_4, x_5, x_6, x_734);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_748;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_723);
lean_dec(x_9);
x_749 = lean_ctor_get(x_736, 0);
lean_inc(x_749);
lean_dec(x_736);
x_750 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_749);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_751 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_750, x_3, x_4, x_5, x_6, x_734);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec(x_751);
x_775 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_776 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed), 9, 2);
lean_closure_set(x_776, 0, x_1);
lean_closure_set(x_776, 1, x_775);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_777 = l_Lean_Meta_forallTelescope___rarg(x_730, x_776, x_3, x_4, x_5, x_6, x_753);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_780 = lean_box(0);
lean_inc(x_726);
x_781 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_781, 0, x_726);
lean_ctor_set(x_781, 1, x_780);
lean_ctor_set(x_781, 2, x_778);
x_782 = lean_box(0);
x_783 = 0;
x_784 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_784, 0, x_781);
lean_ctor_set(x_784, 1, x_752);
lean_ctor_set(x_784, 2, x_782);
lean_ctor_set_uint8(x_784, sizeof(void*)*3, x_783);
x_785 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_785, 0, x_784);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_786 = lean_apply_5(x_719, x_3, x_4, x_5, x_6, x_779);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_789 = l_Lean_Options_empty;
x_790 = l_Lean_Environment_addAndCompile(x_787, x_789, x_785);
lean_dec(x_785);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; 
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_1);
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
lean_dec(x_790);
x_792 = l_Lean_KernelException_toMessageData(x_791, x_789);
x_793 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_792);
x_794 = l_Lean_Format_pretty(x_793, x_789);
x_795 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_795, 0, x_794);
x_796 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_796, 0, x_795);
x_797 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_796, x_3, x_4, x_5, x_6, x_788);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_798 = !lean_is_exclusive(x_797);
if (x_798 == 0)
{
return x_797;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_797, 0);
x_800 = lean_ctor_get(x_797, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_797);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
}
}
else
{
lean_object* x_802; 
x_802 = lean_ctor_get(x_790, 0);
lean_inc(x_802);
lean_dec(x_790);
x_754 = x_802;
x_755 = x_788;
goto block_774;
}
}
else
{
uint8_t x_803; 
lean_dec(x_785);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_803 = !lean_is_exclusive(x_786);
if (x_803 == 0)
{
return x_786;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_786, 0);
x_805 = lean_ctor_get(x_786, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_786);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
else
{
uint8_t x_807; 
lean_dec(x_752);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_807 = !lean_is_exclusive(x_777);
if (x_807 == 0)
{
return x_777;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_777, 0);
x_809 = lean_ctor_get(x_777, 1);
lean_inc(x_809);
lean_inc(x_808);
lean_dec(x_777);
x_810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_810, 0, x_808);
lean_ctor_set(x_810, 1, x_809);
return x_810;
}
}
block_774:
{
lean_object* x_756; lean_object* x_757; 
lean_inc(x_726);
x_756 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_724, x_754, x_710, x_726);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_757 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_756, x_3, x_4, x_5, x_6, x_755);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_758 = lean_ctor_get(x_757, 1);
lean_inc(x_758);
lean_dec(x_757);
x_759 = lean_box(0);
x_760 = l_Lean_mkConst(x_726, x_759);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_760);
x_761 = l_Lean_Meta_inferType(x_760, x_3, x_4, x_5, x_6, x_758);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
x_764 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed), 11, 4);
lean_closure_set(x_764, 0, x_1);
lean_closure_set(x_764, 1, x_731);
lean_closure_set(x_764, 2, x_717);
lean_closure_set(x_764, 3, x_760);
x_765 = l_Lean_Meta_forallTelescope___rarg(x_762, x_764, x_3, x_4, x_5, x_6, x_763);
return x_765;
}
else
{
uint8_t x_766; 
lean_dec(x_760);
lean_dec(x_717);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_766 = !lean_is_exclusive(x_761);
if (x_766 == 0)
{
return x_761;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_761, 0);
x_768 = lean_ctor_get(x_761, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_761);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
else
{
uint8_t x_770; 
lean_dec(x_726);
lean_dec(x_717);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_770 = !lean_is_exclusive(x_757);
if (x_770 == 0)
{
return x_757;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_757, 0);
x_772 = lean_ctor_get(x_757, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_757);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
}
else
{
uint8_t x_811; 
lean_dec(x_730);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_811 = !lean_is_exclusive(x_751);
if (x_811 == 0)
{
return x_751;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_751, 0);
x_813 = lean_ctor_get(x_751, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_751);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
return x_814;
}
}
}
}
}
else
{
uint8_t x_844; 
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_723);
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_844 = !lean_is_exclusive(x_732);
if (x_844 == 0)
{
return x_732;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_732, 0);
x_846 = lean_ctor_get(x_732, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_732);
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
return x_847;
}
}
}
else
{
uint8_t x_848; 
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_723);
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_848 = !lean_is_exclusive(x_727);
if (x_848 == 0)
{
return x_727;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_727, 0);
x_850 = lean_ctor_get(x_727, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_727);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
return x_851;
}
}
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_724);
lean_dec(x_723);
lean_dec(x_719);
lean_dec(x_710);
lean_dec(x_9);
x_852 = lean_ctor_get(x_725, 0);
lean_inc(x_852);
lean_dec(x_725);
x_853 = lean_box(0);
x_854 = l_Lean_mkConst(x_852, x_853);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_854);
x_855 = l_Lean_Meta_inferType(x_854, x_3, x_4, x_5, x_6, x_722);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
lean_dec(x_855);
x_858 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed), 10, 3);
lean_closure_set(x_858, 0, x_1);
lean_closure_set(x_858, 1, x_717);
lean_closure_set(x_858, 2, x_854);
x_859 = l_Lean_Meta_forallTelescope___rarg(x_856, x_858, x_3, x_4, x_5, x_6, x_857);
return x_859;
}
else
{
uint8_t x_860; 
lean_dec(x_854);
lean_dec(x_717);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_860 = !lean_is_exclusive(x_855);
if (x_860 == 0)
{
return x_855;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_855, 0);
x_862 = lean_ctor_get(x_855, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_855);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
}
}
}
else
{
uint8_t x_864; 
lean_dec(x_719);
lean_dec(x_717);
lean_dec(x_710);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_864 = !lean_is_exclusive(x_720);
if (x_864 == 0)
{
return x_720;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_720, 0);
x_866 = lean_ctor_get(x_720, 1);
lean_inc(x_866);
lean_inc(x_865);
lean_dec(x_720);
x_867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_867, 0, x_865);
lean_ctor_set(x_867, 1, x_866);
return x_867;
}
}
}
else
{
lean_object* x_868; 
lean_dec(x_699);
lean_dec(x_1);
x_868 = lean_box(0);
x_700 = x_868;
goto block_709;
}
block_709:
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_700);
x_701 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_702 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_702, 0, x_701);
x_703 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_703, 0, x_702);
x_704 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_705 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
x_706 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_707 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
x_708 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_707, x_3, x_4, x_5, x_6, x_698);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_708;
}
}
case 6:
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_869 = lean_ctor_get(x_8, 1);
lean_inc(x_869);
lean_dec(x_8);
x_870 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16), 8, 1);
lean_closure_set(x_870, 0, x_1);
x_871 = l_Lean_Meta_lambdaTelescope___rarg(x_9, x_870, x_3, x_4, x_5, x_6, x_869);
return x_871;
}
case 7:
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_8, 1);
lean_inc(x_872);
lean_dec(x_8);
x_873 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_873) == 4)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_884 = lean_ctor_get(x_873, 0);
lean_inc(x_884);
lean_dec(x_873);
x_885 = lean_unsigned_to_nat(0u);
x_886 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_885);
x_887 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_886);
x_888 = lean_mk_array(x_886, x_887);
x_889 = lean_unsigned_to_nat(1u);
x_890 = lean_nat_sub(x_886, x_889);
lean_dec(x_886);
lean_inc(x_9);
x_891 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_888, x_890);
x_892 = l_Lean_Meta_isReducible___closed__2;
x_893 = lean_ctor_get(x_892, 0);
lean_inc(x_893);
lean_inc(x_893);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_894 = lean_apply_5(x_893, x_3, x_4, x_5, x_6, x_872);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_897 = lean_ctor_get(x_1, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_1, 2);
lean_inc(x_898);
x_899 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_898, x_895, x_884);
lean_dec(x_895);
if (lean_obj_tag(x_899) == 0)
{
lean_object* x_900; lean_object* x_901; 
lean_inc(x_897);
x_900 = l_Lean_Name_append___main(x_884, x_897);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_884);
x_901 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_884, x_3, x_4, x_5, x_6, x_896);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
lean_dec(x_901);
x_904 = l_Lean_ConstantInfo_type(x_902);
x_905 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_904);
x_906 = l_Lean_Meta_forallTelescope___rarg(x_904, x_905, x_3, x_4, x_5, x_6, x_903);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_990; uint8_t x_991; 
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_906, 1);
lean_inc(x_908);
lean_dec(x_906);
x_990 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_991 = l_Lean_Expr_isConstOf(x_907, x_990);
if (x_991 == 0)
{
lean_object* x_992; uint8_t x_993; 
x_992 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_993 = l_Lean_Expr_isConstOf(x_907, x_992);
lean_dec(x_907);
if (x_993 == 0)
{
lean_object* x_994; 
lean_dec(x_904);
lean_dec(x_902);
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_994 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_908);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_1);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec(x_994);
x_997 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_997, 0, x_897);
x_998 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_999 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_997);
x_1000 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1001 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set(x_1001, 1, x_1000);
x_1002 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1003 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1003, 0, x_1002);
x_1004 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1004, 0, x_1003);
x_1005 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1005, 0, x_1001);
lean_ctor_set(x_1005, 1, x_1004);
x_1006 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1007 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1007, 0, x_1005);
lean_ctor_set(x_1007, 1, x_1006);
x_1008 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1007, x_3, x_4, x_5, x_6, x_996);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1008;
}
else
{
lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_897);
lean_dec(x_9);
x_1009 = lean_ctor_get(x_994, 1);
lean_inc(x_1009);
lean_dec(x_994);
x_1010 = lean_ctor_get(x_995, 0);
lean_inc(x_1010);
lean_dec(x_995);
x_2 = x_1010;
x_7 = x_1009;
goto _start;
}
}
else
{
uint8_t x_1012; 
lean_dec(x_897);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1012 = !lean_is_exclusive(x_994);
if (x_1012 == 0)
{
return x_994;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1013 = lean_ctor_get(x_994, 0);
x_1014 = lean_ctor_get(x_994, 1);
lean_inc(x_1014);
lean_inc(x_1013);
lean_dec(x_994);
x_1015 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1015, 0, x_1013);
lean_ctor_set(x_1015, 1, x_1014);
return x_1015;
}
}
}
else
{
lean_object* x_1016; 
x_1016 = lean_box(0);
x_909 = x_1016;
goto block_989;
}
}
else
{
lean_object* x_1017; 
lean_dec(x_907);
x_1017 = lean_box(0);
x_909 = x_1017;
goto block_989;
}
block_989:
{
lean_object* x_910; 
lean_dec(x_909);
x_910 = l_Lean_ConstantInfo_value_x3f(x_902);
lean_dec(x_902);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_904);
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_1);
x_911 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_911, 0, x_897);
x_912 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_913 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_911);
x_914 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_915 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
x_916 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_917 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_917, 0, x_916);
x_918 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_918, 0, x_917);
x_919 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_919, 0, x_915);
lean_ctor_set(x_919, 1, x_918);
x_920 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_921 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
x_922 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_921, x_3, x_4, x_5, x_6, x_908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_922;
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_897);
lean_dec(x_9);
x_923 = lean_ctor_get(x_910, 0);
lean_inc(x_923);
lean_dec(x_910);
x_924 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_923);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_925 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_924, x_3, x_4, x_5, x_6, x_908);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
x_949 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_950 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed), 9, 2);
lean_closure_set(x_950, 0, x_1);
lean_closure_set(x_950, 1, x_949);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_951 = l_Lean_Meta_forallTelescope___rarg(x_904, x_950, x_3, x_4, x_5, x_6, x_927);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; uint8_t x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_952 = lean_ctor_get(x_951, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec(x_951);
x_954 = lean_box(0);
lean_inc(x_900);
x_955 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_955, 0, x_900);
lean_ctor_set(x_955, 1, x_954);
lean_ctor_set(x_955, 2, x_952);
x_956 = lean_box(0);
x_957 = 0;
x_958 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_958, 0, x_955);
lean_ctor_set(x_958, 1, x_926);
lean_ctor_set(x_958, 2, x_956);
lean_ctor_set_uint8(x_958, sizeof(void*)*3, x_957);
x_959 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_959, 0, x_958);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_960 = lean_apply_5(x_893, x_3, x_4, x_5, x_6, x_953);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
lean_dec(x_960);
x_963 = l_Lean_Options_empty;
x_964 = l_Lean_Environment_addAndCompile(x_961, x_963, x_959);
lean_dec(x_959);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_972; 
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_1);
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
lean_dec(x_964);
x_966 = l_Lean_KernelException_toMessageData(x_965, x_963);
x_967 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_966);
x_968 = l_Lean_Format_pretty(x_967, x_963);
x_969 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_969, 0, x_968);
x_970 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_970, 0, x_969);
x_971 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_970, x_3, x_4, x_5, x_6, x_962);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_972 = !lean_is_exclusive(x_971);
if (x_972 == 0)
{
return x_971;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_973 = lean_ctor_get(x_971, 0);
x_974 = lean_ctor_get(x_971, 1);
lean_inc(x_974);
lean_inc(x_973);
lean_dec(x_971);
x_975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_975, 0, x_973);
lean_ctor_set(x_975, 1, x_974);
return x_975;
}
}
else
{
lean_object* x_976; 
x_976 = lean_ctor_get(x_964, 0);
lean_inc(x_976);
lean_dec(x_964);
x_928 = x_976;
x_929 = x_962;
goto block_948;
}
}
else
{
uint8_t x_977; 
lean_dec(x_959);
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_977 = !lean_is_exclusive(x_960);
if (x_977 == 0)
{
return x_960;
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_978 = lean_ctor_get(x_960, 0);
x_979 = lean_ctor_get(x_960, 1);
lean_inc(x_979);
lean_inc(x_978);
lean_dec(x_960);
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_978);
lean_ctor_set(x_980, 1, x_979);
return x_980;
}
}
}
else
{
uint8_t x_981; 
lean_dec(x_926);
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_981 = !lean_is_exclusive(x_951);
if (x_981 == 0)
{
return x_951;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_982 = lean_ctor_get(x_951, 0);
x_983 = lean_ctor_get(x_951, 1);
lean_inc(x_983);
lean_inc(x_982);
lean_dec(x_951);
x_984 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_984, 0, x_982);
lean_ctor_set(x_984, 1, x_983);
return x_984;
}
}
block_948:
{
lean_object* x_930; lean_object* x_931; 
lean_inc(x_900);
x_930 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_898, x_928, x_884, x_900);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_931 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_930, x_3, x_4, x_5, x_6, x_929);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_932 = lean_ctor_get(x_931, 1);
lean_inc(x_932);
lean_dec(x_931);
x_933 = lean_box(0);
x_934 = l_Lean_mkConst(x_900, x_933);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_934);
x_935 = l_Lean_Meta_inferType(x_934, x_3, x_4, x_5, x_6, x_932);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed), 11, 4);
lean_closure_set(x_938, 0, x_1);
lean_closure_set(x_938, 1, x_905);
lean_closure_set(x_938, 2, x_891);
lean_closure_set(x_938, 3, x_934);
x_939 = l_Lean_Meta_forallTelescope___rarg(x_936, x_938, x_3, x_4, x_5, x_6, x_937);
return x_939;
}
else
{
uint8_t x_940; 
lean_dec(x_934);
lean_dec(x_891);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_940 = !lean_is_exclusive(x_935);
if (x_940 == 0)
{
return x_935;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_941 = lean_ctor_get(x_935, 0);
x_942 = lean_ctor_get(x_935, 1);
lean_inc(x_942);
lean_inc(x_941);
lean_dec(x_935);
x_943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_943, 0, x_941);
lean_ctor_set(x_943, 1, x_942);
return x_943;
}
}
}
else
{
uint8_t x_944; 
lean_dec(x_900);
lean_dec(x_891);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_944 = !lean_is_exclusive(x_931);
if (x_944 == 0)
{
return x_931;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_945 = lean_ctor_get(x_931, 0);
x_946 = lean_ctor_get(x_931, 1);
lean_inc(x_946);
lean_inc(x_945);
lean_dec(x_931);
x_947 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_947, 0, x_945);
lean_ctor_set(x_947, 1, x_946);
return x_947;
}
}
}
}
else
{
uint8_t x_985; 
lean_dec(x_904);
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_985 = !lean_is_exclusive(x_925);
if (x_985 == 0)
{
return x_925;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_986 = lean_ctor_get(x_925, 0);
x_987 = lean_ctor_get(x_925, 1);
lean_inc(x_987);
lean_inc(x_986);
lean_dec(x_925);
x_988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_988, 0, x_986);
lean_ctor_set(x_988, 1, x_987);
return x_988;
}
}
}
}
}
else
{
uint8_t x_1018; 
lean_dec(x_904);
lean_dec(x_902);
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_897);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1018 = !lean_is_exclusive(x_906);
if (x_1018 == 0)
{
return x_906;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_906, 0);
x_1020 = lean_ctor_get(x_906, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_906);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
}
else
{
uint8_t x_1022; 
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_897);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1022 = !lean_is_exclusive(x_901);
if (x_1022 == 0)
{
return x_901;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_901, 0);
x_1024 = lean_ctor_get(x_901, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_901);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_898);
lean_dec(x_897);
lean_dec(x_893);
lean_dec(x_884);
lean_dec(x_9);
x_1026 = lean_ctor_get(x_899, 0);
lean_inc(x_1026);
lean_dec(x_899);
x_1027 = lean_box(0);
x_1028 = l_Lean_mkConst(x_1026, x_1027);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1028);
x_1029 = l_Lean_Meta_inferType(x_1028, x_3, x_4, x_5, x_6, x_896);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed), 10, 3);
lean_closure_set(x_1032, 0, x_1);
lean_closure_set(x_1032, 1, x_891);
lean_closure_set(x_1032, 2, x_1028);
x_1033 = l_Lean_Meta_forallTelescope___rarg(x_1030, x_1032, x_3, x_4, x_5, x_6, x_1031);
return x_1033;
}
else
{
uint8_t x_1034; 
lean_dec(x_1028);
lean_dec(x_891);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1034 = !lean_is_exclusive(x_1029);
if (x_1034 == 0)
{
return x_1029;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_1029, 0);
x_1036 = lean_ctor_get(x_1029, 1);
lean_inc(x_1036);
lean_inc(x_1035);
lean_dec(x_1029);
x_1037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1037, 0, x_1035);
lean_ctor_set(x_1037, 1, x_1036);
return x_1037;
}
}
}
}
else
{
uint8_t x_1038; 
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_884);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1038 = !lean_is_exclusive(x_894);
if (x_1038 == 0)
{
return x_894;
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_894, 0);
x_1040 = lean_ctor_get(x_894, 1);
lean_inc(x_1040);
lean_inc(x_1039);
lean_dec(x_894);
x_1041 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1041, 0, x_1039);
lean_ctor_set(x_1041, 1, x_1040);
return x_1041;
}
}
}
else
{
lean_object* x_1042; 
lean_dec(x_873);
lean_dec(x_1);
x_1042 = lean_box(0);
x_874 = x_1042;
goto block_883;
}
block_883:
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_874);
x_875 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_876 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_876, 0, x_875);
x_877 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_877, 0, x_876);
x_878 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_879 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_879, 0, x_878);
lean_ctor_set(x_879, 1, x_877);
x_880 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_881 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_880);
x_882 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_881, x_3, x_4, x_5, x_6, x_872);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_882;
}
}
case 8:
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1043 = lean_ctor_get(x_8, 1);
lean_inc(x_1043);
lean_dec(x_8);
x_1044 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1044) == 4)
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1055 = lean_ctor_get(x_1044, 0);
lean_inc(x_1055);
lean_dec(x_1044);
x_1056 = lean_unsigned_to_nat(0u);
x_1057 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1056);
x_1058 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1057);
x_1059 = lean_mk_array(x_1057, x_1058);
x_1060 = lean_unsigned_to_nat(1u);
x_1061 = lean_nat_sub(x_1057, x_1060);
lean_dec(x_1057);
lean_inc(x_9);
x_1062 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1059, x_1061);
x_1063 = l_Lean_Meta_isReducible___closed__2;
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
lean_inc(x_1064);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1065 = lean_apply_5(x_1064, x_3, x_4, x_5, x_6, x_1043);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
x_1068 = lean_ctor_get(x_1, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1, 2);
lean_inc(x_1069);
x_1070 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1069, x_1066, x_1055);
lean_dec(x_1066);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; 
lean_inc(x_1068);
x_1071 = l_Lean_Name_append___main(x_1055, x_1068);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1055);
x_1072 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1055, x_3, x_4, x_5, x_6, x_1067);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1072, 1);
lean_inc(x_1074);
lean_dec(x_1072);
x_1075 = l_Lean_ConstantInfo_type(x_1073);
x_1076 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1075);
x_1077 = l_Lean_Meta_forallTelescope___rarg(x_1075, x_1076, x_3, x_4, x_5, x_6, x_1074);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1161; uint8_t x_1162; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
x_1161 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1162 = l_Lean_Expr_isConstOf(x_1078, x_1161);
if (x_1162 == 0)
{
lean_object* x_1163; uint8_t x_1164; 
x_1163 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1164 = l_Lean_Expr_isConstOf(x_1078, x_1163);
lean_dec(x_1078);
if (x_1164 == 0)
{
lean_object* x_1165; 
lean_dec(x_1075);
lean_dec(x_1073);
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1165 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1079);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
if (lean_obj_tag(x_1166) == 0)
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
lean_dec(x_1);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1168, 0, x_1068);
x_1169 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1170 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1170, 0, x_1169);
lean_ctor_set(x_1170, 1, x_1168);
x_1171 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1172 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
x_1173 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1174 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1174, 0, x_1173);
x_1175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1175, 0, x_1174);
x_1176 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1176, 0, x_1172);
lean_ctor_set(x_1176, 1, x_1175);
x_1177 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1178 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
x_1179 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1178, x_3, x_4, x_5, x_6, x_1167);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1179;
}
else
{
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_1068);
lean_dec(x_9);
x_1180 = lean_ctor_get(x_1165, 1);
lean_inc(x_1180);
lean_dec(x_1165);
x_1181 = lean_ctor_get(x_1166, 0);
lean_inc(x_1181);
lean_dec(x_1166);
x_2 = x_1181;
x_7 = x_1180;
goto _start;
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1068);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1183 = !lean_is_exclusive(x_1165);
if (x_1183 == 0)
{
return x_1165;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1165, 0);
x_1185 = lean_ctor_get(x_1165, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1165);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
lean_object* x_1187; 
x_1187 = lean_box(0);
x_1080 = x_1187;
goto block_1160;
}
}
else
{
lean_object* x_1188; 
lean_dec(x_1078);
x_1188 = lean_box(0);
x_1080 = x_1188;
goto block_1160;
}
block_1160:
{
lean_object* x_1081; 
lean_dec(x_1080);
x_1081 = l_Lean_ConstantInfo_value_x3f(x_1073);
lean_dec(x_1073);
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_1075);
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_1);
x_1082 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1082, 0, x_1068);
x_1083 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1084 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1084, 1, x_1082);
x_1085 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1086 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1086, 0, x_1084);
lean_ctor_set(x_1086, 1, x_1085);
x_1087 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1088 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1088, 0, x_1087);
x_1089 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1089, 0, x_1088);
x_1090 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1090, 0, x_1086);
lean_ctor_set(x_1090, 1, x_1089);
x_1091 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1092 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
x_1093 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1092, x_3, x_4, x_5, x_6, x_1079);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1093;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
lean_dec(x_1068);
lean_dec(x_9);
x_1094 = lean_ctor_get(x_1081, 0);
lean_inc(x_1094);
lean_dec(x_1081);
x_1095 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1094);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1096 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1095, x_3, x_4, x_5, x_6, x_1079);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1096, 1);
lean_inc(x_1098);
lean_dec(x_1096);
x_1120 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1121 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed), 9, 2);
lean_closure_set(x_1121, 0, x_1);
lean_closure_set(x_1121, 1, x_1120);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1122 = l_Lean_Meta_forallTelescope___rarg(x_1075, x_1121, x_3, x_4, x_5, x_6, x_1098);
if (lean_obj_tag(x_1122) == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
lean_dec(x_1122);
x_1125 = lean_box(0);
lean_inc(x_1071);
x_1126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1126, 0, x_1071);
lean_ctor_set(x_1126, 1, x_1125);
lean_ctor_set(x_1126, 2, x_1123);
x_1127 = lean_box(0);
x_1128 = 0;
x_1129 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1129, 0, x_1126);
lean_ctor_set(x_1129, 1, x_1097);
lean_ctor_set(x_1129, 2, x_1127);
lean_ctor_set_uint8(x_1129, sizeof(void*)*3, x_1128);
x_1130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1130, 0, x_1129);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1131 = lean_apply_5(x_1064, x_3, x_4, x_5, x_6, x_1124);
if (lean_obj_tag(x_1131) == 0)
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1131, 1);
lean_inc(x_1133);
lean_dec(x_1131);
x_1134 = l_Lean_Options_empty;
x_1135 = l_Lean_Environment_addAndCompile(x_1132, x_1134, x_1130);
lean_dec(x_1130);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; uint8_t x_1143; 
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_1);
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
lean_dec(x_1135);
x_1137 = l_Lean_KernelException_toMessageData(x_1136, x_1134);
x_1138 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1137);
x_1139 = l_Lean_Format_pretty(x_1138, x_1134);
x_1140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1140, 0, x_1139);
x_1141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1141, 0, x_1140);
x_1142 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1141, x_3, x_4, x_5, x_6, x_1133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1143 = !lean_is_exclusive(x_1142);
if (x_1143 == 0)
{
return x_1142;
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1144 = lean_ctor_get(x_1142, 0);
x_1145 = lean_ctor_get(x_1142, 1);
lean_inc(x_1145);
lean_inc(x_1144);
lean_dec(x_1142);
x_1146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1146, 0, x_1144);
lean_ctor_set(x_1146, 1, x_1145);
return x_1146;
}
}
else
{
lean_object* x_1147; 
x_1147 = lean_ctor_get(x_1135, 0);
lean_inc(x_1147);
lean_dec(x_1135);
x_1099 = x_1147;
x_1100 = x_1133;
goto block_1119;
}
}
else
{
uint8_t x_1148; 
lean_dec(x_1130);
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1148 = !lean_is_exclusive(x_1131);
if (x_1148 == 0)
{
return x_1131;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1149 = lean_ctor_get(x_1131, 0);
x_1150 = lean_ctor_get(x_1131, 1);
lean_inc(x_1150);
lean_inc(x_1149);
lean_dec(x_1131);
x_1151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1151, 0, x_1149);
lean_ctor_set(x_1151, 1, x_1150);
return x_1151;
}
}
}
else
{
uint8_t x_1152; 
lean_dec(x_1097);
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1152 = !lean_is_exclusive(x_1122);
if (x_1152 == 0)
{
return x_1122;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1153 = lean_ctor_get(x_1122, 0);
x_1154 = lean_ctor_get(x_1122, 1);
lean_inc(x_1154);
lean_inc(x_1153);
lean_dec(x_1122);
x_1155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
return x_1155;
}
}
block_1119:
{
lean_object* x_1101; lean_object* x_1102; 
lean_inc(x_1071);
x_1101 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1069, x_1099, x_1055, x_1071);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1102 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_1101, x_3, x_4, x_5, x_6, x_1100);
if (lean_obj_tag(x_1102) == 0)
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
x_1103 = lean_ctor_get(x_1102, 1);
lean_inc(x_1103);
lean_dec(x_1102);
x_1104 = lean_box(0);
x_1105 = l_Lean_mkConst(x_1071, x_1104);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1105);
x_1106 = l_Lean_Meta_inferType(x_1105, x_3, x_4, x_5, x_6, x_1103);
if (lean_obj_tag(x_1106) == 0)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1107 = lean_ctor_get(x_1106, 0);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_1106, 1);
lean_inc(x_1108);
lean_dec(x_1106);
x_1109 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed), 11, 4);
lean_closure_set(x_1109, 0, x_1);
lean_closure_set(x_1109, 1, x_1076);
lean_closure_set(x_1109, 2, x_1062);
lean_closure_set(x_1109, 3, x_1105);
x_1110 = l_Lean_Meta_forallTelescope___rarg(x_1107, x_1109, x_3, x_4, x_5, x_6, x_1108);
return x_1110;
}
else
{
uint8_t x_1111; 
lean_dec(x_1105);
lean_dec(x_1062);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1111 = !lean_is_exclusive(x_1106);
if (x_1111 == 0)
{
return x_1106;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1106, 0);
x_1113 = lean_ctor_get(x_1106, 1);
lean_inc(x_1113);
lean_inc(x_1112);
lean_dec(x_1106);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
return x_1114;
}
}
}
else
{
uint8_t x_1115; 
lean_dec(x_1071);
lean_dec(x_1062);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1115 = !lean_is_exclusive(x_1102);
if (x_1115 == 0)
{
return x_1102;
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1102, 0);
x_1117 = lean_ctor_get(x_1102, 1);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1102);
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1117);
return x_1118;
}
}
}
}
else
{
uint8_t x_1156; 
lean_dec(x_1075);
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1156 = !lean_is_exclusive(x_1096);
if (x_1156 == 0)
{
return x_1096;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_1096, 0);
x_1158 = lean_ctor_get(x_1096, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_1096);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
}
}
}
}
}
else
{
uint8_t x_1189; 
lean_dec(x_1075);
lean_dec(x_1073);
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1189 = !lean_is_exclusive(x_1077);
if (x_1189 == 0)
{
return x_1077;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1190 = lean_ctor_get(x_1077, 0);
x_1191 = lean_ctor_get(x_1077, 1);
lean_inc(x_1191);
lean_inc(x_1190);
lean_dec(x_1077);
x_1192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1192, 0, x_1190);
lean_ctor_set(x_1192, 1, x_1191);
return x_1192;
}
}
}
else
{
uint8_t x_1193; 
lean_dec(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1193 = !lean_is_exclusive(x_1072);
if (x_1193 == 0)
{
return x_1072;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1194 = lean_ctor_get(x_1072, 0);
x_1195 = lean_ctor_get(x_1072, 1);
lean_inc(x_1195);
lean_inc(x_1194);
lean_dec(x_1072);
x_1196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1196, 0, x_1194);
lean_ctor_set(x_1196, 1, x_1195);
return x_1196;
}
}
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1064);
lean_dec(x_1055);
lean_dec(x_9);
x_1197 = lean_ctor_get(x_1070, 0);
lean_inc(x_1197);
lean_dec(x_1070);
x_1198 = lean_box(0);
x_1199 = l_Lean_mkConst(x_1197, x_1198);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1199);
x_1200 = l_Lean_Meta_inferType(x_1199, x_3, x_4, x_5, x_6, x_1067);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec(x_1200);
x_1203 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed), 10, 3);
lean_closure_set(x_1203, 0, x_1);
lean_closure_set(x_1203, 1, x_1062);
lean_closure_set(x_1203, 2, x_1199);
x_1204 = l_Lean_Meta_forallTelescope___rarg(x_1201, x_1203, x_3, x_4, x_5, x_6, x_1202);
return x_1204;
}
else
{
uint8_t x_1205; 
lean_dec(x_1199);
lean_dec(x_1062);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1205 = !lean_is_exclusive(x_1200);
if (x_1205 == 0)
{
return x_1200;
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1206 = lean_ctor_get(x_1200, 0);
x_1207 = lean_ctor_get(x_1200, 1);
lean_inc(x_1207);
lean_inc(x_1206);
lean_dec(x_1200);
x_1208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1208, 0, x_1206);
lean_ctor_set(x_1208, 1, x_1207);
return x_1208;
}
}
}
}
else
{
uint8_t x_1209; 
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_1055);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1209 = !lean_is_exclusive(x_1065);
if (x_1209 == 0)
{
return x_1065;
}
else
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1210 = lean_ctor_get(x_1065, 0);
x_1211 = lean_ctor_get(x_1065, 1);
lean_inc(x_1211);
lean_inc(x_1210);
lean_dec(x_1065);
x_1212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1212, 0, x_1210);
lean_ctor_set(x_1212, 1, x_1211);
return x_1212;
}
}
}
else
{
lean_object* x_1213; 
lean_dec(x_1044);
lean_dec(x_1);
x_1213 = lean_box(0);
x_1045 = x_1213;
goto block_1054;
}
block_1054:
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1045);
x_1046 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1047 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1047, 0, x_1046);
x_1048 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1048, 0, x_1047);
x_1049 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1050 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1050, 0, x_1049);
lean_ctor_set(x_1050, 1, x_1048);
x_1051 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1052 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1052, 0, x_1050);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1052, x_3, x_4, x_5, x_6, x_1043);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1053;
}
}
case 9:
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1214 = lean_ctor_get(x_8, 1);
lean_inc(x_1214);
lean_dec(x_8);
x_1215 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1215) == 4)
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1226 = lean_ctor_get(x_1215, 0);
lean_inc(x_1226);
lean_dec(x_1215);
x_1227 = lean_unsigned_to_nat(0u);
x_1228 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1227);
x_1229 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1228);
x_1230 = lean_mk_array(x_1228, x_1229);
x_1231 = lean_unsigned_to_nat(1u);
x_1232 = lean_nat_sub(x_1228, x_1231);
lean_dec(x_1228);
lean_inc(x_9);
x_1233 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1230, x_1232);
x_1234 = l_Lean_Meta_isReducible___closed__2;
x_1235 = lean_ctor_get(x_1234, 0);
lean_inc(x_1235);
lean_inc(x_1235);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1236 = lean_apply_5(x_1235, x_3, x_4, x_5, x_6, x_1214);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
lean_dec(x_1236);
x_1239 = lean_ctor_get(x_1, 0);
lean_inc(x_1239);
x_1240 = lean_ctor_get(x_1, 2);
lean_inc(x_1240);
x_1241 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1240, x_1237, x_1226);
lean_dec(x_1237);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; 
lean_inc(x_1239);
x_1242 = l_Lean_Name_append___main(x_1226, x_1239);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1226);
x_1243 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1226, x_3, x_4, x_5, x_6, x_1238);
if (lean_obj_tag(x_1243) == 0)
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1244 = lean_ctor_get(x_1243, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1243, 1);
lean_inc(x_1245);
lean_dec(x_1243);
x_1246 = l_Lean_ConstantInfo_type(x_1244);
x_1247 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1246);
x_1248 = l_Lean_Meta_forallTelescope___rarg(x_1246, x_1247, x_3, x_4, x_5, x_6, x_1245);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1332; uint8_t x_1333; 
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1248, 1);
lean_inc(x_1250);
lean_dec(x_1248);
x_1332 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1333 = l_Lean_Expr_isConstOf(x_1249, x_1332);
if (x_1333 == 0)
{
lean_object* x_1334; uint8_t x_1335; 
x_1334 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1335 = l_Lean_Expr_isConstOf(x_1249, x_1334);
lean_dec(x_1249);
if (x_1335 == 0)
{
lean_object* x_1336; 
lean_dec(x_1246);
lean_dec(x_1244);
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1336 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1250);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; 
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
if (lean_obj_tag(x_1337) == 0)
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
lean_dec(x_1);
x_1338 = lean_ctor_get(x_1336, 1);
lean_inc(x_1338);
lean_dec(x_1336);
x_1339 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1339, 0, x_1239);
x_1340 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1341 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1341, 0, x_1340);
lean_ctor_set(x_1341, 1, x_1339);
x_1342 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1343 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1343, 0, x_1341);
lean_ctor_set(x_1343, 1, x_1342);
x_1344 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1345 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1345, 0, x_1344);
x_1346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1346, 0, x_1345);
x_1347 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1347, 0, x_1343);
lean_ctor_set(x_1347, 1, x_1346);
x_1348 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1349 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1349, 0, x_1347);
lean_ctor_set(x_1349, 1, x_1348);
x_1350 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1349, x_3, x_4, x_5, x_6, x_1338);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1350;
}
else
{
lean_object* x_1351; lean_object* x_1352; 
lean_dec(x_1239);
lean_dec(x_9);
x_1351 = lean_ctor_get(x_1336, 1);
lean_inc(x_1351);
lean_dec(x_1336);
x_1352 = lean_ctor_get(x_1337, 0);
lean_inc(x_1352);
lean_dec(x_1337);
x_2 = x_1352;
x_7 = x_1351;
goto _start;
}
}
else
{
uint8_t x_1354; 
lean_dec(x_1239);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1354 = !lean_is_exclusive(x_1336);
if (x_1354 == 0)
{
return x_1336;
}
else
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
x_1355 = lean_ctor_get(x_1336, 0);
x_1356 = lean_ctor_get(x_1336, 1);
lean_inc(x_1356);
lean_inc(x_1355);
lean_dec(x_1336);
x_1357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1357, 0, x_1355);
lean_ctor_set(x_1357, 1, x_1356);
return x_1357;
}
}
}
else
{
lean_object* x_1358; 
x_1358 = lean_box(0);
x_1251 = x_1358;
goto block_1331;
}
}
else
{
lean_object* x_1359; 
lean_dec(x_1249);
x_1359 = lean_box(0);
x_1251 = x_1359;
goto block_1331;
}
block_1331:
{
lean_object* x_1252; 
lean_dec(x_1251);
x_1252 = l_Lean_ConstantInfo_value_x3f(x_1244);
lean_dec(x_1244);
if (lean_obj_tag(x_1252) == 0)
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
lean_dec(x_1246);
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_1);
x_1253 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1253, 0, x_1239);
x_1254 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1255, 0, x_1254);
lean_ctor_set(x_1255, 1, x_1253);
x_1256 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1257 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1257, 0, x_1255);
lean_ctor_set(x_1257, 1, x_1256);
x_1258 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1259 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1259, 0, x_1258);
x_1260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1260, 0, x_1259);
x_1261 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1261, 0, x_1257);
lean_ctor_set(x_1261, 1, x_1260);
x_1262 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1263 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1263, 0, x_1261);
lean_ctor_set(x_1263, 1, x_1262);
x_1264 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1263, x_3, x_4, x_5, x_6, x_1250);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1264;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
lean_dec(x_1239);
lean_dec(x_9);
x_1265 = lean_ctor_get(x_1252, 0);
lean_inc(x_1265);
lean_dec(x_1252);
x_1266 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1265);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1267 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1266, x_3, x_4, x_5, x_6, x_1250);
if (lean_obj_tag(x_1267) == 0)
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
x_1269 = lean_ctor_get(x_1267, 1);
lean_inc(x_1269);
lean_dec(x_1267);
x_1291 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1292 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed), 9, 2);
lean_closure_set(x_1292, 0, x_1);
lean_closure_set(x_1292, 1, x_1291);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1293 = l_Lean_Meta_forallTelescope___rarg(x_1246, x_1292, x_3, x_4, x_5, x_6, x_1269);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1293, 1);
lean_inc(x_1295);
lean_dec(x_1293);
x_1296 = lean_box(0);
lean_inc(x_1242);
x_1297 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1297, 0, x_1242);
lean_ctor_set(x_1297, 1, x_1296);
lean_ctor_set(x_1297, 2, x_1294);
x_1298 = lean_box(0);
x_1299 = 0;
x_1300 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1300, 0, x_1297);
lean_ctor_set(x_1300, 1, x_1268);
lean_ctor_set(x_1300, 2, x_1298);
lean_ctor_set_uint8(x_1300, sizeof(void*)*3, x_1299);
x_1301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1301, 0, x_1300);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1302 = lean_apply_5(x_1235, x_3, x_4, x_5, x_6, x_1295);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec(x_1302);
x_1305 = l_Lean_Options_empty;
x_1306 = l_Lean_Environment_addAndCompile(x_1303, x_1305, x_1301);
lean_dec(x_1301);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; uint8_t x_1314; 
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_1);
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
lean_dec(x_1306);
x_1308 = l_Lean_KernelException_toMessageData(x_1307, x_1305);
x_1309 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1308);
x_1310 = l_Lean_Format_pretty(x_1309, x_1305);
x_1311 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1311, 0, x_1310);
x_1312 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1312, 0, x_1311);
x_1313 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1312, x_3, x_4, x_5, x_6, x_1304);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1314 = !lean_is_exclusive(x_1313);
if (x_1314 == 0)
{
return x_1313;
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1315 = lean_ctor_get(x_1313, 0);
x_1316 = lean_ctor_get(x_1313, 1);
lean_inc(x_1316);
lean_inc(x_1315);
lean_dec(x_1313);
x_1317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1317, 0, x_1315);
lean_ctor_set(x_1317, 1, x_1316);
return x_1317;
}
}
else
{
lean_object* x_1318; 
x_1318 = lean_ctor_get(x_1306, 0);
lean_inc(x_1318);
lean_dec(x_1306);
x_1270 = x_1318;
x_1271 = x_1304;
goto block_1290;
}
}
else
{
uint8_t x_1319; 
lean_dec(x_1301);
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1319 = !lean_is_exclusive(x_1302);
if (x_1319 == 0)
{
return x_1302;
}
else
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1320 = lean_ctor_get(x_1302, 0);
x_1321 = lean_ctor_get(x_1302, 1);
lean_inc(x_1321);
lean_inc(x_1320);
lean_dec(x_1302);
x_1322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1322, 0, x_1320);
lean_ctor_set(x_1322, 1, x_1321);
return x_1322;
}
}
}
else
{
uint8_t x_1323; 
lean_dec(x_1268);
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1323 = !lean_is_exclusive(x_1293);
if (x_1323 == 0)
{
return x_1293;
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
x_1324 = lean_ctor_get(x_1293, 0);
x_1325 = lean_ctor_get(x_1293, 1);
lean_inc(x_1325);
lean_inc(x_1324);
lean_dec(x_1293);
x_1326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1326, 0, x_1324);
lean_ctor_set(x_1326, 1, x_1325);
return x_1326;
}
}
block_1290:
{
lean_object* x_1272; lean_object* x_1273; 
lean_inc(x_1242);
x_1272 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1240, x_1270, x_1226, x_1242);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1273 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_1272, x_3, x_4, x_5, x_6, x_1271);
if (lean_obj_tag(x_1273) == 0)
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1274 = lean_ctor_get(x_1273, 1);
lean_inc(x_1274);
lean_dec(x_1273);
x_1275 = lean_box(0);
x_1276 = l_Lean_mkConst(x_1242, x_1275);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1276);
x_1277 = l_Lean_Meta_inferType(x_1276, x_3, x_4, x_5, x_6, x_1274);
if (lean_obj_tag(x_1277) == 0)
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; 
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
lean_dec(x_1277);
x_1280 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed), 11, 4);
lean_closure_set(x_1280, 0, x_1);
lean_closure_set(x_1280, 1, x_1247);
lean_closure_set(x_1280, 2, x_1233);
lean_closure_set(x_1280, 3, x_1276);
x_1281 = l_Lean_Meta_forallTelescope___rarg(x_1278, x_1280, x_3, x_4, x_5, x_6, x_1279);
return x_1281;
}
else
{
uint8_t x_1282; 
lean_dec(x_1276);
lean_dec(x_1233);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1282 = !lean_is_exclusive(x_1277);
if (x_1282 == 0)
{
return x_1277;
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
x_1283 = lean_ctor_get(x_1277, 0);
x_1284 = lean_ctor_get(x_1277, 1);
lean_inc(x_1284);
lean_inc(x_1283);
lean_dec(x_1277);
x_1285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1285, 0, x_1283);
lean_ctor_set(x_1285, 1, x_1284);
return x_1285;
}
}
}
else
{
uint8_t x_1286; 
lean_dec(x_1242);
lean_dec(x_1233);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1286 = !lean_is_exclusive(x_1273);
if (x_1286 == 0)
{
return x_1273;
}
else
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1287 = lean_ctor_get(x_1273, 0);
x_1288 = lean_ctor_get(x_1273, 1);
lean_inc(x_1288);
lean_inc(x_1287);
lean_dec(x_1273);
x_1289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1289, 0, x_1287);
lean_ctor_set(x_1289, 1, x_1288);
return x_1289;
}
}
}
}
else
{
uint8_t x_1327; 
lean_dec(x_1246);
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1327 = !lean_is_exclusive(x_1267);
if (x_1327 == 0)
{
return x_1267;
}
else
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
x_1328 = lean_ctor_get(x_1267, 0);
x_1329 = lean_ctor_get(x_1267, 1);
lean_inc(x_1329);
lean_inc(x_1328);
lean_dec(x_1267);
x_1330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1330, 0, x_1328);
lean_ctor_set(x_1330, 1, x_1329);
return x_1330;
}
}
}
}
}
else
{
uint8_t x_1360; 
lean_dec(x_1246);
lean_dec(x_1244);
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1239);
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1360 = !lean_is_exclusive(x_1248);
if (x_1360 == 0)
{
return x_1248;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1361 = lean_ctor_get(x_1248, 0);
x_1362 = lean_ctor_get(x_1248, 1);
lean_inc(x_1362);
lean_inc(x_1361);
lean_dec(x_1248);
x_1363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1363, 0, x_1361);
lean_ctor_set(x_1363, 1, x_1362);
return x_1363;
}
}
}
else
{
uint8_t x_1364; 
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1239);
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1364 = !lean_is_exclusive(x_1243);
if (x_1364 == 0)
{
return x_1243;
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1365 = lean_ctor_get(x_1243, 0);
x_1366 = lean_ctor_get(x_1243, 1);
lean_inc(x_1366);
lean_inc(x_1365);
lean_dec(x_1243);
x_1367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1367, 0, x_1365);
lean_ctor_set(x_1367, 1, x_1366);
return x_1367;
}
}
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
lean_dec(x_1240);
lean_dec(x_1239);
lean_dec(x_1235);
lean_dec(x_1226);
lean_dec(x_9);
x_1368 = lean_ctor_get(x_1241, 0);
lean_inc(x_1368);
lean_dec(x_1241);
x_1369 = lean_box(0);
x_1370 = l_Lean_mkConst(x_1368, x_1369);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1370);
x_1371 = l_Lean_Meta_inferType(x_1370, x_3, x_4, x_5, x_6, x_1238);
if (lean_obj_tag(x_1371) == 0)
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
lean_dec(x_1371);
x_1374 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed), 10, 3);
lean_closure_set(x_1374, 0, x_1);
lean_closure_set(x_1374, 1, x_1233);
lean_closure_set(x_1374, 2, x_1370);
x_1375 = l_Lean_Meta_forallTelescope___rarg(x_1372, x_1374, x_3, x_4, x_5, x_6, x_1373);
return x_1375;
}
else
{
uint8_t x_1376; 
lean_dec(x_1370);
lean_dec(x_1233);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1376 = !lean_is_exclusive(x_1371);
if (x_1376 == 0)
{
return x_1371;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1377 = lean_ctor_get(x_1371, 0);
x_1378 = lean_ctor_get(x_1371, 1);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_1371);
x_1379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
return x_1379;
}
}
}
}
else
{
uint8_t x_1380; 
lean_dec(x_1235);
lean_dec(x_1233);
lean_dec(x_1226);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1380 = !lean_is_exclusive(x_1236);
if (x_1380 == 0)
{
return x_1236;
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
x_1381 = lean_ctor_get(x_1236, 0);
x_1382 = lean_ctor_get(x_1236, 1);
lean_inc(x_1382);
lean_inc(x_1381);
lean_dec(x_1236);
x_1383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1383, 0, x_1381);
lean_ctor_set(x_1383, 1, x_1382);
return x_1383;
}
}
}
else
{
lean_object* x_1384; 
lean_dec(x_1215);
lean_dec(x_1);
x_1384 = lean_box(0);
x_1216 = x_1384;
goto block_1225;
}
block_1225:
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_1216);
x_1217 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1218 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1218, 0, x_1217);
x_1219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1219, 0, x_1218);
x_1220 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1221 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1223 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1223, 0, x_1221);
lean_ctor_set(x_1223, 1, x_1222);
x_1224 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1223, x_3, x_4, x_5, x_6, x_1214);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1224;
}
}
case 10:
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_8, 1);
lean_inc(x_1385);
lean_dec(x_8);
x_1386 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1386) == 4)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1397 = lean_ctor_get(x_1386, 0);
lean_inc(x_1397);
lean_dec(x_1386);
x_1398 = lean_unsigned_to_nat(0u);
x_1399 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1398);
x_1400 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1399);
x_1401 = lean_mk_array(x_1399, x_1400);
x_1402 = lean_unsigned_to_nat(1u);
x_1403 = lean_nat_sub(x_1399, x_1402);
lean_dec(x_1399);
lean_inc(x_9);
x_1404 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1401, x_1403);
x_1405 = l_Lean_Meta_isReducible___closed__2;
x_1406 = lean_ctor_get(x_1405, 0);
lean_inc(x_1406);
lean_inc(x_1406);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1407 = lean_apply_5(x_1406, x_3, x_4, x_5, x_6, x_1385);
if (lean_obj_tag(x_1407) == 0)
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
x_1408 = lean_ctor_get(x_1407, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1407, 1);
lean_inc(x_1409);
lean_dec(x_1407);
x_1410 = lean_ctor_get(x_1, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1, 2);
lean_inc(x_1411);
x_1412 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1411, x_1408, x_1397);
lean_dec(x_1408);
if (lean_obj_tag(x_1412) == 0)
{
lean_object* x_1413; lean_object* x_1414; 
lean_inc(x_1410);
x_1413 = l_Lean_Name_append___main(x_1397, x_1410);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1397);
x_1414 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1397, x_3, x_4, x_5, x_6, x_1409);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
lean_dec(x_1414);
x_1417 = l_Lean_ConstantInfo_type(x_1415);
x_1418 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1417);
x_1419 = l_Lean_Meta_forallTelescope___rarg(x_1417, x_1418, x_3, x_4, x_5, x_6, x_1416);
if (lean_obj_tag(x_1419) == 0)
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1503; uint8_t x_1504; 
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
lean_dec(x_1419);
x_1503 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1504 = l_Lean_Expr_isConstOf(x_1420, x_1503);
if (x_1504 == 0)
{
lean_object* x_1505; uint8_t x_1506; 
x_1505 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1506 = l_Lean_Expr_isConstOf(x_1420, x_1505);
lean_dec(x_1420);
if (x_1506 == 0)
{
lean_object* x_1507; 
lean_dec(x_1417);
lean_dec(x_1415);
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1507 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1421);
if (lean_obj_tag(x_1507) == 0)
{
lean_object* x_1508; 
x_1508 = lean_ctor_get(x_1507, 0);
lean_inc(x_1508);
if (lean_obj_tag(x_1508) == 0)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; 
lean_dec(x_1);
x_1509 = lean_ctor_get(x_1507, 1);
lean_inc(x_1509);
lean_dec(x_1507);
x_1510 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1510, 0, x_1410);
x_1511 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1512 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1512, 0, x_1511);
lean_ctor_set(x_1512, 1, x_1510);
x_1513 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1514 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1514, 0, x_1512);
lean_ctor_set(x_1514, 1, x_1513);
x_1515 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1516 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1516, 0, x_1515);
x_1517 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1517, 0, x_1516);
x_1518 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1518, 0, x_1514);
lean_ctor_set(x_1518, 1, x_1517);
x_1519 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1520 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set(x_1520, 1, x_1519);
x_1521 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1520, x_3, x_4, x_5, x_6, x_1509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1521;
}
else
{
lean_object* x_1522; lean_object* x_1523; 
lean_dec(x_1410);
lean_dec(x_9);
x_1522 = lean_ctor_get(x_1507, 1);
lean_inc(x_1522);
lean_dec(x_1507);
x_1523 = lean_ctor_get(x_1508, 0);
lean_inc(x_1523);
lean_dec(x_1508);
x_2 = x_1523;
x_7 = x_1522;
goto _start;
}
}
else
{
uint8_t x_1525; 
lean_dec(x_1410);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1525 = !lean_is_exclusive(x_1507);
if (x_1525 == 0)
{
return x_1507;
}
else
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1526 = lean_ctor_get(x_1507, 0);
x_1527 = lean_ctor_get(x_1507, 1);
lean_inc(x_1527);
lean_inc(x_1526);
lean_dec(x_1507);
x_1528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1528, 0, x_1526);
lean_ctor_set(x_1528, 1, x_1527);
return x_1528;
}
}
}
else
{
lean_object* x_1529; 
x_1529 = lean_box(0);
x_1422 = x_1529;
goto block_1502;
}
}
else
{
lean_object* x_1530; 
lean_dec(x_1420);
x_1530 = lean_box(0);
x_1422 = x_1530;
goto block_1502;
}
block_1502:
{
lean_object* x_1423; 
lean_dec(x_1422);
x_1423 = l_Lean_ConstantInfo_value_x3f(x_1415);
lean_dec(x_1415);
if (lean_obj_tag(x_1423) == 0)
{
lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
lean_dec(x_1417);
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_1);
x_1424 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1424, 0, x_1410);
x_1425 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1426 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1426, 0, x_1425);
lean_ctor_set(x_1426, 1, x_1424);
x_1427 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1428 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1428, 0, x_1426);
lean_ctor_set(x_1428, 1, x_1427);
x_1429 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1430 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1430, 0, x_1429);
x_1431 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1431, 0, x_1430);
x_1432 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1432, 0, x_1428);
lean_ctor_set(x_1432, 1, x_1431);
x_1433 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1434 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1434, 0, x_1432);
lean_ctor_set(x_1434, 1, x_1433);
x_1435 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1434, x_3, x_4, x_5, x_6, x_1421);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1435;
}
else
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
lean_dec(x_1410);
lean_dec(x_9);
x_1436 = lean_ctor_get(x_1423, 0);
lean_inc(x_1436);
lean_dec(x_1423);
x_1437 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1436);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1438 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1437, x_3, x_4, x_5, x_6, x_1421);
if (lean_obj_tag(x_1438) == 0)
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; 
x_1439 = lean_ctor_get(x_1438, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1438, 1);
lean_inc(x_1440);
lean_dec(x_1438);
x_1462 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1463 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed), 9, 2);
lean_closure_set(x_1463, 0, x_1);
lean_closure_set(x_1463, 1, x_1462);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1464 = l_Lean_Meta_forallTelescope___rarg(x_1417, x_1463, x_3, x_4, x_5, x_6, x_1440);
if (lean_obj_tag(x_1464) == 0)
{
lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; uint8_t x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
x_1465 = lean_ctor_get(x_1464, 0);
lean_inc(x_1465);
x_1466 = lean_ctor_get(x_1464, 1);
lean_inc(x_1466);
lean_dec(x_1464);
x_1467 = lean_box(0);
lean_inc(x_1413);
x_1468 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1468, 0, x_1413);
lean_ctor_set(x_1468, 1, x_1467);
lean_ctor_set(x_1468, 2, x_1465);
x_1469 = lean_box(0);
x_1470 = 0;
x_1471 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1471, 0, x_1468);
lean_ctor_set(x_1471, 1, x_1439);
lean_ctor_set(x_1471, 2, x_1469);
lean_ctor_set_uint8(x_1471, sizeof(void*)*3, x_1470);
x_1472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1472, 0, x_1471);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1473 = lean_apply_5(x_1406, x_3, x_4, x_5, x_6, x_1466);
if (lean_obj_tag(x_1473) == 0)
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; 
x_1474 = lean_ctor_get(x_1473, 0);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1473, 1);
lean_inc(x_1475);
lean_dec(x_1473);
x_1476 = l_Lean_Options_empty;
x_1477 = l_Lean_Environment_addAndCompile(x_1474, x_1476, x_1472);
lean_dec(x_1472);
if (lean_obj_tag(x_1477) == 0)
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; uint8_t x_1485; 
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_1);
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
lean_dec(x_1477);
x_1479 = l_Lean_KernelException_toMessageData(x_1478, x_1476);
x_1480 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1479);
x_1481 = l_Lean_Format_pretty(x_1480, x_1476);
x_1482 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1482, 0, x_1481);
x_1483 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1483, 0, x_1482);
x_1484 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1483, x_3, x_4, x_5, x_6, x_1475);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1485 = !lean_is_exclusive(x_1484);
if (x_1485 == 0)
{
return x_1484;
}
else
{
lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
x_1486 = lean_ctor_get(x_1484, 0);
x_1487 = lean_ctor_get(x_1484, 1);
lean_inc(x_1487);
lean_inc(x_1486);
lean_dec(x_1484);
x_1488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1488, 0, x_1486);
lean_ctor_set(x_1488, 1, x_1487);
return x_1488;
}
}
else
{
lean_object* x_1489; 
x_1489 = lean_ctor_get(x_1477, 0);
lean_inc(x_1489);
lean_dec(x_1477);
x_1441 = x_1489;
x_1442 = x_1475;
goto block_1461;
}
}
else
{
uint8_t x_1490; 
lean_dec(x_1472);
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1490 = !lean_is_exclusive(x_1473);
if (x_1490 == 0)
{
return x_1473;
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
x_1491 = lean_ctor_get(x_1473, 0);
x_1492 = lean_ctor_get(x_1473, 1);
lean_inc(x_1492);
lean_inc(x_1491);
lean_dec(x_1473);
x_1493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1493, 0, x_1491);
lean_ctor_set(x_1493, 1, x_1492);
return x_1493;
}
}
}
else
{
uint8_t x_1494; 
lean_dec(x_1439);
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1494 = !lean_is_exclusive(x_1464);
if (x_1494 == 0)
{
return x_1464;
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1495 = lean_ctor_get(x_1464, 0);
x_1496 = lean_ctor_get(x_1464, 1);
lean_inc(x_1496);
lean_inc(x_1495);
lean_dec(x_1464);
x_1497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1497, 0, x_1495);
lean_ctor_set(x_1497, 1, x_1496);
return x_1497;
}
}
block_1461:
{
lean_object* x_1443; lean_object* x_1444; 
lean_inc(x_1413);
x_1443 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1411, x_1441, x_1397, x_1413);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1444 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_1443, x_3, x_4, x_5, x_6, x_1442);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; 
x_1445 = lean_ctor_get(x_1444, 1);
lean_inc(x_1445);
lean_dec(x_1444);
x_1446 = lean_box(0);
x_1447 = l_Lean_mkConst(x_1413, x_1446);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1447);
x_1448 = l_Lean_Meta_inferType(x_1447, x_3, x_4, x_5, x_6, x_1445);
if (lean_obj_tag(x_1448) == 0)
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; 
x_1449 = lean_ctor_get(x_1448, 0);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1448, 1);
lean_inc(x_1450);
lean_dec(x_1448);
x_1451 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed), 11, 4);
lean_closure_set(x_1451, 0, x_1);
lean_closure_set(x_1451, 1, x_1418);
lean_closure_set(x_1451, 2, x_1404);
lean_closure_set(x_1451, 3, x_1447);
x_1452 = l_Lean_Meta_forallTelescope___rarg(x_1449, x_1451, x_3, x_4, x_5, x_6, x_1450);
return x_1452;
}
else
{
uint8_t x_1453; 
lean_dec(x_1447);
lean_dec(x_1404);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1453 = !lean_is_exclusive(x_1448);
if (x_1453 == 0)
{
return x_1448;
}
else
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
x_1454 = lean_ctor_get(x_1448, 0);
x_1455 = lean_ctor_get(x_1448, 1);
lean_inc(x_1455);
lean_inc(x_1454);
lean_dec(x_1448);
x_1456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1456, 0, x_1454);
lean_ctor_set(x_1456, 1, x_1455);
return x_1456;
}
}
}
else
{
uint8_t x_1457; 
lean_dec(x_1413);
lean_dec(x_1404);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1457 = !lean_is_exclusive(x_1444);
if (x_1457 == 0)
{
return x_1444;
}
else
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1458 = lean_ctor_get(x_1444, 0);
x_1459 = lean_ctor_get(x_1444, 1);
lean_inc(x_1459);
lean_inc(x_1458);
lean_dec(x_1444);
x_1460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1460, 0, x_1458);
lean_ctor_set(x_1460, 1, x_1459);
return x_1460;
}
}
}
}
else
{
uint8_t x_1498; 
lean_dec(x_1417);
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1498 = !lean_is_exclusive(x_1438);
if (x_1498 == 0)
{
return x_1438;
}
else
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
x_1499 = lean_ctor_get(x_1438, 0);
x_1500 = lean_ctor_get(x_1438, 1);
lean_inc(x_1500);
lean_inc(x_1499);
lean_dec(x_1438);
x_1501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1501, 0, x_1499);
lean_ctor_set(x_1501, 1, x_1500);
return x_1501;
}
}
}
}
}
else
{
uint8_t x_1531; 
lean_dec(x_1417);
lean_dec(x_1415);
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1531 = !lean_is_exclusive(x_1419);
if (x_1531 == 0)
{
return x_1419;
}
else
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1532 = lean_ctor_get(x_1419, 0);
x_1533 = lean_ctor_get(x_1419, 1);
lean_inc(x_1533);
lean_inc(x_1532);
lean_dec(x_1419);
x_1534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1534, 0, x_1532);
lean_ctor_set(x_1534, 1, x_1533);
return x_1534;
}
}
}
else
{
uint8_t x_1535; 
lean_dec(x_1413);
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1535 = !lean_is_exclusive(x_1414);
if (x_1535 == 0)
{
return x_1414;
}
else
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
x_1536 = lean_ctor_get(x_1414, 0);
x_1537 = lean_ctor_get(x_1414, 1);
lean_inc(x_1537);
lean_inc(x_1536);
lean_dec(x_1414);
x_1538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1538, 0, x_1536);
lean_ctor_set(x_1538, 1, x_1537);
return x_1538;
}
}
}
else
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1406);
lean_dec(x_1397);
lean_dec(x_9);
x_1539 = lean_ctor_get(x_1412, 0);
lean_inc(x_1539);
lean_dec(x_1412);
x_1540 = lean_box(0);
x_1541 = l_Lean_mkConst(x_1539, x_1540);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1541);
x_1542 = l_Lean_Meta_inferType(x_1541, x_3, x_4, x_5, x_6, x_1409);
if (lean_obj_tag(x_1542) == 0)
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
x_1543 = lean_ctor_get(x_1542, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1542, 1);
lean_inc(x_1544);
lean_dec(x_1542);
x_1545 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed), 10, 3);
lean_closure_set(x_1545, 0, x_1);
lean_closure_set(x_1545, 1, x_1404);
lean_closure_set(x_1545, 2, x_1541);
x_1546 = l_Lean_Meta_forallTelescope___rarg(x_1543, x_1545, x_3, x_4, x_5, x_6, x_1544);
return x_1546;
}
else
{
uint8_t x_1547; 
lean_dec(x_1541);
lean_dec(x_1404);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1547 = !lean_is_exclusive(x_1542);
if (x_1547 == 0)
{
return x_1542;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
x_1548 = lean_ctor_get(x_1542, 0);
x_1549 = lean_ctor_get(x_1542, 1);
lean_inc(x_1549);
lean_inc(x_1548);
lean_dec(x_1542);
x_1550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1550, 0, x_1548);
lean_ctor_set(x_1550, 1, x_1549);
return x_1550;
}
}
}
}
else
{
uint8_t x_1551; 
lean_dec(x_1406);
lean_dec(x_1404);
lean_dec(x_1397);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1551 = !lean_is_exclusive(x_1407);
if (x_1551 == 0)
{
return x_1407;
}
else
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1552 = lean_ctor_get(x_1407, 0);
x_1553 = lean_ctor_get(x_1407, 1);
lean_inc(x_1553);
lean_inc(x_1552);
lean_dec(x_1407);
x_1554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1554, 0, x_1552);
lean_ctor_set(x_1554, 1, x_1553);
return x_1554;
}
}
}
else
{
lean_object* x_1555; 
lean_dec(x_1386);
lean_dec(x_1);
x_1555 = lean_box(0);
x_1387 = x_1555;
goto block_1396;
}
block_1396:
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
lean_dec(x_1387);
x_1388 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1389 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1389, 0, x_1388);
x_1390 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1390, 0, x_1389);
x_1391 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1392, 0, x_1391);
lean_ctor_set(x_1392, 1, x_1390);
x_1393 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1394 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set(x_1394, 1, x_1393);
x_1395 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1394, x_3, x_4, x_5, x_6, x_1385);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1395;
}
}
case 11:
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1556 = lean_ctor_get(x_8, 1);
lean_inc(x_1556);
lean_dec(x_8);
x_1557 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1557) == 4)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; 
x_1568 = lean_ctor_get(x_1557, 0);
lean_inc(x_1568);
lean_dec(x_1557);
x_1569 = lean_unsigned_to_nat(0u);
x_1570 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1569);
x_1571 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1570);
x_1572 = lean_mk_array(x_1570, x_1571);
x_1573 = lean_unsigned_to_nat(1u);
x_1574 = lean_nat_sub(x_1570, x_1573);
lean_dec(x_1570);
lean_inc(x_9);
x_1575 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1572, x_1574);
x_1576 = l_Lean_Meta_isReducible___closed__2;
x_1577 = lean_ctor_get(x_1576, 0);
lean_inc(x_1577);
lean_inc(x_1577);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1578 = lean_apply_5(x_1577, x_3, x_4, x_5, x_6, x_1556);
if (lean_obj_tag(x_1578) == 0)
{
lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1579 = lean_ctor_get(x_1578, 0);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_1578, 1);
lean_inc(x_1580);
lean_dec(x_1578);
x_1581 = lean_ctor_get(x_1, 0);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_1, 2);
lean_inc(x_1582);
x_1583 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1582, x_1579, x_1568);
lean_dec(x_1579);
if (lean_obj_tag(x_1583) == 0)
{
lean_object* x_1584; lean_object* x_1585; 
lean_inc(x_1581);
x_1584 = l_Lean_Name_append___main(x_1568, x_1581);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1568);
x_1585 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1568, x_3, x_4, x_5, x_6, x_1580);
if (lean_obj_tag(x_1585) == 0)
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; 
x_1586 = lean_ctor_get(x_1585, 0);
lean_inc(x_1586);
x_1587 = lean_ctor_get(x_1585, 1);
lean_inc(x_1587);
lean_dec(x_1585);
x_1588 = l_Lean_ConstantInfo_type(x_1586);
x_1589 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1588);
x_1590 = l_Lean_Meta_forallTelescope___rarg(x_1588, x_1589, x_3, x_4, x_5, x_6, x_1587);
if (lean_obj_tag(x_1590) == 0)
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1674; uint8_t x_1675; 
x_1591 = lean_ctor_get(x_1590, 0);
lean_inc(x_1591);
x_1592 = lean_ctor_get(x_1590, 1);
lean_inc(x_1592);
lean_dec(x_1590);
x_1674 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1675 = l_Lean_Expr_isConstOf(x_1591, x_1674);
if (x_1675 == 0)
{
lean_object* x_1676; uint8_t x_1677; 
x_1676 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1677 = l_Lean_Expr_isConstOf(x_1591, x_1676);
lean_dec(x_1591);
if (x_1677 == 0)
{
lean_object* x_1678; 
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1678 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1592);
if (lean_obj_tag(x_1678) == 0)
{
lean_object* x_1679; 
x_1679 = lean_ctor_get(x_1678, 0);
lean_inc(x_1679);
if (lean_obj_tag(x_1679) == 0)
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; 
lean_dec(x_1);
x_1680 = lean_ctor_get(x_1678, 1);
lean_inc(x_1680);
lean_dec(x_1678);
x_1681 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1681, 0, x_1581);
x_1682 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1683 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1683, 0, x_1682);
lean_ctor_set(x_1683, 1, x_1681);
x_1684 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1685 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1685, 0, x_1683);
lean_ctor_set(x_1685, 1, x_1684);
x_1686 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1687 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1687, 0, x_1686);
x_1688 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1688, 0, x_1687);
x_1689 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1689, 0, x_1685);
lean_ctor_set(x_1689, 1, x_1688);
x_1690 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1691 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1691, 0, x_1689);
lean_ctor_set(x_1691, 1, x_1690);
x_1692 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1691, x_3, x_4, x_5, x_6, x_1680);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1692;
}
else
{
lean_object* x_1693; lean_object* x_1694; 
lean_dec(x_1581);
lean_dec(x_9);
x_1693 = lean_ctor_get(x_1678, 1);
lean_inc(x_1693);
lean_dec(x_1678);
x_1694 = lean_ctor_get(x_1679, 0);
lean_inc(x_1694);
lean_dec(x_1679);
x_2 = x_1694;
x_7 = x_1693;
goto _start;
}
}
else
{
uint8_t x_1696; 
lean_dec(x_1581);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1696 = !lean_is_exclusive(x_1678);
if (x_1696 == 0)
{
return x_1678;
}
else
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
x_1697 = lean_ctor_get(x_1678, 0);
x_1698 = lean_ctor_get(x_1678, 1);
lean_inc(x_1698);
lean_inc(x_1697);
lean_dec(x_1678);
x_1699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1699, 0, x_1697);
lean_ctor_set(x_1699, 1, x_1698);
return x_1699;
}
}
}
else
{
lean_object* x_1700; 
x_1700 = lean_box(0);
x_1593 = x_1700;
goto block_1673;
}
}
else
{
lean_object* x_1701; 
lean_dec(x_1591);
x_1701 = lean_box(0);
x_1593 = x_1701;
goto block_1673;
}
block_1673:
{
lean_object* x_1594; 
lean_dec(x_1593);
x_1594 = l_Lean_ConstantInfo_value_x3f(x_1586);
lean_dec(x_1586);
if (lean_obj_tag(x_1594) == 0)
{
lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
lean_dec(x_1588);
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_1);
x_1595 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1595, 0, x_1581);
x_1596 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1597 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1597, 0, x_1596);
lean_ctor_set(x_1597, 1, x_1595);
x_1598 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1599 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1599, 0, x_1597);
lean_ctor_set(x_1599, 1, x_1598);
x_1600 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1601 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1601, 0, x_1600);
x_1602 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1602, 0, x_1601);
x_1603 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1603, 0, x_1599);
lean_ctor_set(x_1603, 1, x_1602);
x_1604 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1605 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1605, 0, x_1603);
lean_ctor_set(x_1605, 1, x_1604);
x_1606 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1605, x_3, x_4, x_5, x_6, x_1592);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1606;
}
else
{
lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; 
lean_dec(x_1581);
lean_dec(x_9);
x_1607 = lean_ctor_get(x_1594, 0);
lean_inc(x_1607);
lean_dec(x_1594);
x_1608 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1607);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1609 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1608, x_3, x_4, x_5, x_6, x_1592);
if (lean_obj_tag(x_1609) == 0)
{
lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
x_1610 = lean_ctor_get(x_1609, 0);
lean_inc(x_1610);
x_1611 = lean_ctor_get(x_1609, 1);
lean_inc(x_1611);
lean_dec(x_1609);
x_1633 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1634 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed), 9, 2);
lean_closure_set(x_1634, 0, x_1);
lean_closure_set(x_1634, 1, x_1633);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1635 = l_Lean_Meta_forallTelescope___rarg(x_1588, x_1634, x_3, x_4, x_5, x_6, x_1611);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; uint8_t x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1635, 1);
lean_inc(x_1637);
lean_dec(x_1635);
x_1638 = lean_box(0);
lean_inc(x_1584);
x_1639 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1639, 0, x_1584);
lean_ctor_set(x_1639, 1, x_1638);
lean_ctor_set(x_1639, 2, x_1636);
x_1640 = lean_box(0);
x_1641 = 0;
x_1642 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1642, 0, x_1639);
lean_ctor_set(x_1642, 1, x_1610);
lean_ctor_set(x_1642, 2, x_1640);
lean_ctor_set_uint8(x_1642, sizeof(void*)*3, x_1641);
x_1643 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1643, 0, x_1642);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1644 = lean_apply_5(x_1577, x_3, x_4, x_5, x_6, x_1637);
if (lean_obj_tag(x_1644) == 0)
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
x_1645 = lean_ctor_get(x_1644, 0);
lean_inc(x_1645);
x_1646 = lean_ctor_get(x_1644, 1);
lean_inc(x_1646);
lean_dec(x_1644);
x_1647 = l_Lean_Options_empty;
x_1648 = l_Lean_Environment_addAndCompile(x_1645, x_1647, x_1643);
lean_dec(x_1643);
if (lean_obj_tag(x_1648) == 0)
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; uint8_t x_1656; 
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_1);
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
lean_dec(x_1648);
x_1650 = l_Lean_KernelException_toMessageData(x_1649, x_1647);
x_1651 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1650);
x_1652 = l_Lean_Format_pretty(x_1651, x_1647);
x_1653 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1653, 0, x_1652);
x_1654 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1654, 0, x_1653);
x_1655 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1654, x_3, x_4, x_5, x_6, x_1646);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1656 = !lean_is_exclusive(x_1655);
if (x_1656 == 0)
{
return x_1655;
}
else
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; 
x_1657 = lean_ctor_get(x_1655, 0);
x_1658 = lean_ctor_get(x_1655, 1);
lean_inc(x_1658);
lean_inc(x_1657);
lean_dec(x_1655);
x_1659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1659, 0, x_1657);
lean_ctor_set(x_1659, 1, x_1658);
return x_1659;
}
}
else
{
lean_object* x_1660; 
x_1660 = lean_ctor_get(x_1648, 0);
lean_inc(x_1660);
lean_dec(x_1648);
x_1612 = x_1660;
x_1613 = x_1646;
goto block_1632;
}
}
else
{
uint8_t x_1661; 
lean_dec(x_1643);
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1661 = !lean_is_exclusive(x_1644);
if (x_1661 == 0)
{
return x_1644;
}
else
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; 
x_1662 = lean_ctor_get(x_1644, 0);
x_1663 = lean_ctor_get(x_1644, 1);
lean_inc(x_1663);
lean_inc(x_1662);
lean_dec(x_1644);
x_1664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1664, 0, x_1662);
lean_ctor_set(x_1664, 1, x_1663);
return x_1664;
}
}
}
else
{
uint8_t x_1665; 
lean_dec(x_1610);
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1665 = !lean_is_exclusive(x_1635);
if (x_1665 == 0)
{
return x_1635;
}
else
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
x_1666 = lean_ctor_get(x_1635, 0);
x_1667 = lean_ctor_get(x_1635, 1);
lean_inc(x_1667);
lean_inc(x_1666);
lean_dec(x_1635);
x_1668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1668, 0, x_1666);
lean_ctor_set(x_1668, 1, x_1667);
return x_1668;
}
}
block_1632:
{
lean_object* x_1614; lean_object* x_1615; 
lean_inc(x_1584);
x_1614 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1582, x_1612, x_1568, x_1584);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1615 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_1614, x_3, x_4, x_5, x_6, x_1613);
if (lean_obj_tag(x_1615) == 0)
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; 
x_1616 = lean_ctor_get(x_1615, 1);
lean_inc(x_1616);
lean_dec(x_1615);
x_1617 = lean_box(0);
x_1618 = l_Lean_mkConst(x_1584, x_1617);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1618);
x_1619 = l_Lean_Meta_inferType(x_1618, x_3, x_4, x_5, x_6, x_1616);
if (lean_obj_tag(x_1619) == 0)
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; 
x_1620 = lean_ctor_get(x_1619, 0);
lean_inc(x_1620);
x_1621 = lean_ctor_get(x_1619, 1);
lean_inc(x_1621);
lean_dec(x_1619);
x_1622 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed), 11, 4);
lean_closure_set(x_1622, 0, x_1);
lean_closure_set(x_1622, 1, x_1589);
lean_closure_set(x_1622, 2, x_1575);
lean_closure_set(x_1622, 3, x_1618);
x_1623 = l_Lean_Meta_forallTelescope___rarg(x_1620, x_1622, x_3, x_4, x_5, x_6, x_1621);
return x_1623;
}
else
{
uint8_t x_1624; 
lean_dec(x_1618);
lean_dec(x_1575);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1624 = !lean_is_exclusive(x_1619);
if (x_1624 == 0)
{
return x_1619;
}
else
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
x_1625 = lean_ctor_get(x_1619, 0);
x_1626 = lean_ctor_get(x_1619, 1);
lean_inc(x_1626);
lean_inc(x_1625);
lean_dec(x_1619);
x_1627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1627, 0, x_1625);
lean_ctor_set(x_1627, 1, x_1626);
return x_1627;
}
}
}
else
{
uint8_t x_1628; 
lean_dec(x_1584);
lean_dec(x_1575);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1628 = !lean_is_exclusive(x_1615);
if (x_1628 == 0)
{
return x_1615;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
x_1629 = lean_ctor_get(x_1615, 0);
x_1630 = lean_ctor_get(x_1615, 1);
lean_inc(x_1630);
lean_inc(x_1629);
lean_dec(x_1615);
x_1631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1631, 0, x_1629);
lean_ctor_set(x_1631, 1, x_1630);
return x_1631;
}
}
}
}
else
{
uint8_t x_1669; 
lean_dec(x_1588);
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1669 = !lean_is_exclusive(x_1609);
if (x_1669 == 0)
{
return x_1609;
}
else
{
lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; 
x_1670 = lean_ctor_get(x_1609, 0);
x_1671 = lean_ctor_get(x_1609, 1);
lean_inc(x_1671);
lean_inc(x_1670);
lean_dec(x_1609);
x_1672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1672, 0, x_1670);
lean_ctor_set(x_1672, 1, x_1671);
return x_1672;
}
}
}
}
}
else
{
uint8_t x_1702; 
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1581);
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1702 = !lean_is_exclusive(x_1590);
if (x_1702 == 0)
{
return x_1590;
}
else
{
lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
x_1703 = lean_ctor_get(x_1590, 0);
x_1704 = lean_ctor_get(x_1590, 1);
lean_inc(x_1704);
lean_inc(x_1703);
lean_dec(x_1590);
x_1705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1705, 0, x_1703);
lean_ctor_set(x_1705, 1, x_1704);
return x_1705;
}
}
}
else
{
uint8_t x_1706; 
lean_dec(x_1584);
lean_dec(x_1582);
lean_dec(x_1581);
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1706 = !lean_is_exclusive(x_1585);
if (x_1706 == 0)
{
return x_1585;
}
else
{
lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; 
x_1707 = lean_ctor_get(x_1585, 0);
x_1708 = lean_ctor_get(x_1585, 1);
lean_inc(x_1708);
lean_inc(x_1707);
lean_dec(x_1585);
x_1709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1709, 0, x_1707);
lean_ctor_set(x_1709, 1, x_1708);
return x_1709;
}
}
}
else
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; 
lean_dec(x_1582);
lean_dec(x_1581);
lean_dec(x_1577);
lean_dec(x_1568);
lean_dec(x_9);
x_1710 = lean_ctor_get(x_1583, 0);
lean_inc(x_1710);
lean_dec(x_1583);
x_1711 = lean_box(0);
x_1712 = l_Lean_mkConst(x_1710, x_1711);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1712);
x_1713 = l_Lean_Meta_inferType(x_1712, x_3, x_4, x_5, x_6, x_1580);
if (lean_obj_tag(x_1713) == 0)
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; 
x_1714 = lean_ctor_get(x_1713, 0);
lean_inc(x_1714);
x_1715 = lean_ctor_get(x_1713, 1);
lean_inc(x_1715);
lean_dec(x_1713);
x_1716 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed), 10, 3);
lean_closure_set(x_1716, 0, x_1);
lean_closure_set(x_1716, 1, x_1575);
lean_closure_set(x_1716, 2, x_1712);
x_1717 = l_Lean_Meta_forallTelescope___rarg(x_1714, x_1716, x_3, x_4, x_5, x_6, x_1715);
return x_1717;
}
else
{
uint8_t x_1718; 
lean_dec(x_1712);
lean_dec(x_1575);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1718 = !lean_is_exclusive(x_1713);
if (x_1718 == 0)
{
return x_1713;
}
else
{
lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; 
x_1719 = lean_ctor_get(x_1713, 0);
x_1720 = lean_ctor_get(x_1713, 1);
lean_inc(x_1720);
lean_inc(x_1719);
lean_dec(x_1713);
x_1721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1721, 0, x_1719);
lean_ctor_set(x_1721, 1, x_1720);
return x_1721;
}
}
}
}
else
{
uint8_t x_1722; 
lean_dec(x_1577);
lean_dec(x_1575);
lean_dec(x_1568);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1722 = !lean_is_exclusive(x_1578);
if (x_1722 == 0)
{
return x_1578;
}
else
{
lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; 
x_1723 = lean_ctor_get(x_1578, 0);
x_1724 = lean_ctor_get(x_1578, 1);
lean_inc(x_1724);
lean_inc(x_1723);
lean_dec(x_1578);
x_1725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1725, 0, x_1723);
lean_ctor_set(x_1725, 1, x_1724);
return x_1725;
}
}
}
else
{
lean_object* x_1726; 
lean_dec(x_1557);
lean_dec(x_1);
x_1726 = lean_box(0);
x_1558 = x_1726;
goto block_1567;
}
block_1567:
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; 
lean_dec(x_1558);
x_1559 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1560 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1560, 0, x_1559);
x_1561 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1561, 0, x_1560);
x_1562 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1563 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1563, 0, x_1562);
lean_ctor_set(x_1563, 1, x_1561);
x_1564 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1565 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1565, 0, x_1563);
lean_ctor_set(x_1565, 1, x_1564);
x_1566 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1565, x_3, x_4, x_5, x_6, x_1556);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1566;
}
}
default: 
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
x_1727 = lean_ctor_get(x_8, 1);
lean_inc(x_1727);
lean_dec(x_8);
x_1728 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1728) == 4)
{
lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; 
x_1739 = lean_ctor_get(x_1728, 0);
lean_inc(x_1739);
lean_dec(x_1728);
x_1740 = lean_unsigned_to_nat(0u);
x_1741 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1740);
x_1742 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1741);
x_1743 = lean_mk_array(x_1741, x_1742);
x_1744 = lean_unsigned_to_nat(1u);
x_1745 = lean_nat_sub(x_1741, x_1744);
lean_dec(x_1741);
lean_inc(x_9);
x_1746 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1743, x_1745);
x_1747 = l_Lean_Meta_isReducible___closed__2;
x_1748 = lean_ctor_get(x_1747, 0);
lean_inc(x_1748);
lean_inc(x_1748);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1749 = lean_apply_5(x_1748, x_3, x_4, x_5, x_6, x_1727);
if (lean_obj_tag(x_1749) == 0)
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
x_1750 = lean_ctor_get(x_1749, 0);
lean_inc(x_1750);
x_1751 = lean_ctor_get(x_1749, 1);
lean_inc(x_1751);
lean_dec(x_1749);
x_1752 = lean_ctor_get(x_1, 0);
lean_inc(x_1752);
x_1753 = lean_ctor_get(x_1, 2);
lean_inc(x_1753);
x_1754 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1753, x_1750, x_1739);
lean_dec(x_1750);
if (lean_obj_tag(x_1754) == 0)
{
lean_object* x_1755; lean_object* x_1756; 
lean_inc(x_1752);
x_1755 = l_Lean_Name_append___main(x_1739, x_1752);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1739);
x_1756 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1739, x_3, x_4, x_5, x_6, x_1751);
if (lean_obj_tag(x_1756) == 0)
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; 
x_1757 = lean_ctor_get(x_1756, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1756, 1);
lean_inc(x_1758);
lean_dec(x_1756);
x_1759 = l_Lean_ConstantInfo_type(x_1757);
x_1760 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1759);
x_1761 = l_Lean_Meta_forallTelescope___rarg(x_1759, x_1760, x_3, x_4, x_5, x_6, x_1758);
if (lean_obj_tag(x_1761) == 0)
{
lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1845; uint8_t x_1846; 
x_1762 = lean_ctor_get(x_1761, 0);
lean_inc(x_1762);
x_1763 = lean_ctor_get(x_1761, 1);
lean_inc(x_1763);
lean_dec(x_1761);
x_1845 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1846 = l_Lean_Expr_isConstOf(x_1762, x_1845);
if (x_1846 == 0)
{
lean_object* x_1847; uint8_t x_1848; 
x_1847 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1848 = l_Lean_Expr_isConstOf(x_1762, x_1847);
lean_dec(x_1762);
if (x_1848 == 0)
{
lean_object* x_1849; 
lean_dec(x_1759);
lean_dec(x_1757);
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1849 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1763);
if (lean_obj_tag(x_1849) == 0)
{
lean_object* x_1850; 
x_1850 = lean_ctor_get(x_1849, 0);
lean_inc(x_1850);
if (lean_obj_tag(x_1850) == 0)
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; 
lean_dec(x_1);
x_1851 = lean_ctor_get(x_1849, 1);
lean_inc(x_1851);
lean_dec(x_1849);
x_1852 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1852, 0, x_1752);
x_1853 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1854 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1854, 0, x_1853);
lean_ctor_set(x_1854, 1, x_1852);
x_1855 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1856 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1856, 0, x_1854);
lean_ctor_set(x_1856, 1, x_1855);
x_1857 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1858 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1858, 0, x_1857);
x_1859 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1859, 0, x_1858);
x_1860 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1860, 0, x_1856);
lean_ctor_set(x_1860, 1, x_1859);
x_1861 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1862 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1862, 0, x_1860);
lean_ctor_set(x_1862, 1, x_1861);
x_1863 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1862, x_3, x_4, x_5, x_6, x_1851);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1863;
}
else
{
lean_object* x_1864; lean_object* x_1865; 
lean_dec(x_1752);
lean_dec(x_9);
x_1864 = lean_ctor_get(x_1849, 1);
lean_inc(x_1864);
lean_dec(x_1849);
x_1865 = lean_ctor_get(x_1850, 0);
lean_inc(x_1865);
lean_dec(x_1850);
x_2 = x_1865;
x_7 = x_1864;
goto _start;
}
}
else
{
uint8_t x_1867; 
lean_dec(x_1752);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1867 = !lean_is_exclusive(x_1849);
if (x_1867 == 0)
{
return x_1849;
}
else
{
lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; 
x_1868 = lean_ctor_get(x_1849, 0);
x_1869 = lean_ctor_get(x_1849, 1);
lean_inc(x_1869);
lean_inc(x_1868);
lean_dec(x_1849);
x_1870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1870, 0, x_1868);
lean_ctor_set(x_1870, 1, x_1869);
return x_1870;
}
}
}
else
{
lean_object* x_1871; 
x_1871 = lean_box(0);
x_1764 = x_1871;
goto block_1844;
}
}
else
{
lean_object* x_1872; 
lean_dec(x_1762);
x_1872 = lean_box(0);
x_1764 = x_1872;
goto block_1844;
}
block_1844:
{
lean_object* x_1765; 
lean_dec(x_1764);
x_1765 = l_Lean_ConstantInfo_value_x3f(x_1757);
lean_dec(x_1757);
if (lean_obj_tag(x_1765) == 0)
{
lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
lean_dec(x_1759);
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_1);
x_1766 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1766, 0, x_1752);
x_1767 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1768 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1768, 0, x_1767);
lean_ctor_set(x_1768, 1, x_1766);
x_1769 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1770 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1770, 0, x_1768);
lean_ctor_set(x_1770, 1, x_1769);
x_1771 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1772 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1772, 0, x_1771);
x_1773 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1773, 0, x_1772);
x_1774 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1774, 0, x_1770);
lean_ctor_set(x_1774, 1, x_1773);
x_1775 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1776 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1776, 0, x_1774);
lean_ctor_set(x_1776, 1, x_1775);
x_1777 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1776, x_3, x_4, x_5, x_6, x_1763);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1777;
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; 
lean_dec(x_1752);
lean_dec(x_9);
x_1778 = lean_ctor_get(x_1765, 0);
lean_inc(x_1778);
lean_dec(x_1765);
x_1779 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1778);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1780 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1779, x_3, x_4, x_5, x_6, x_1763);
if (lean_obj_tag(x_1780) == 0)
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; 
x_1781 = lean_ctor_get(x_1780, 0);
lean_inc(x_1781);
x_1782 = lean_ctor_get(x_1780, 1);
lean_inc(x_1782);
lean_dec(x_1780);
x_1804 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1805 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed), 9, 2);
lean_closure_set(x_1805, 0, x_1);
lean_closure_set(x_1805, 1, x_1804);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1806 = l_Lean_Meta_forallTelescope___rarg(x_1759, x_1805, x_3, x_4, x_5, x_6, x_1782);
if (lean_obj_tag(x_1806) == 0)
{
lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; uint8_t x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; 
x_1807 = lean_ctor_get(x_1806, 0);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1806, 1);
lean_inc(x_1808);
lean_dec(x_1806);
x_1809 = lean_box(0);
lean_inc(x_1755);
x_1810 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1810, 0, x_1755);
lean_ctor_set(x_1810, 1, x_1809);
lean_ctor_set(x_1810, 2, x_1807);
x_1811 = lean_box(0);
x_1812 = 0;
x_1813 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1813, 0, x_1810);
lean_ctor_set(x_1813, 1, x_1781);
lean_ctor_set(x_1813, 2, x_1811);
lean_ctor_set_uint8(x_1813, sizeof(void*)*3, x_1812);
x_1814 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1814, 0, x_1813);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1815 = lean_apply_5(x_1748, x_3, x_4, x_5, x_6, x_1808);
if (lean_obj_tag(x_1815) == 0)
{
lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; 
x_1816 = lean_ctor_get(x_1815, 0);
lean_inc(x_1816);
x_1817 = lean_ctor_get(x_1815, 1);
lean_inc(x_1817);
lean_dec(x_1815);
x_1818 = l_Lean_Options_empty;
x_1819 = l_Lean_Environment_addAndCompile(x_1816, x_1818, x_1814);
lean_dec(x_1814);
if (lean_obj_tag(x_1819) == 0)
{
lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; uint8_t x_1827; 
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_1);
x_1820 = lean_ctor_get(x_1819, 0);
lean_inc(x_1820);
lean_dec(x_1819);
x_1821 = l_Lean_KernelException_toMessageData(x_1820, x_1818);
x_1822 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1821);
x_1823 = l_Lean_Format_pretty(x_1822, x_1818);
x_1824 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1824, 0, x_1823);
x_1825 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1825, 0, x_1824);
x_1826 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1825, x_3, x_4, x_5, x_6, x_1817);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1827 = !lean_is_exclusive(x_1826);
if (x_1827 == 0)
{
return x_1826;
}
else
{
lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; 
x_1828 = lean_ctor_get(x_1826, 0);
x_1829 = lean_ctor_get(x_1826, 1);
lean_inc(x_1829);
lean_inc(x_1828);
lean_dec(x_1826);
x_1830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1830, 0, x_1828);
lean_ctor_set(x_1830, 1, x_1829);
return x_1830;
}
}
else
{
lean_object* x_1831; 
x_1831 = lean_ctor_get(x_1819, 0);
lean_inc(x_1831);
lean_dec(x_1819);
x_1783 = x_1831;
x_1784 = x_1817;
goto block_1803;
}
}
else
{
uint8_t x_1832; 
lean_dec(x_1814);
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1832 = !lean_is_exclusive(x_1815);
if (x_1832 == 0)
{
return x_1815;
}
else
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; 
x_1833 = lean_ctor_get(x_1815, 0);
x_1834 = lean_ctor_get(x_1815, 1);
lean_inc(x_1834);
lean_inc(x_1833);
lean_dec(x_1815);
x_1835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1835, 0, x_1833);
lean_ctor_set(x_1835, 1, x_1834);
return x_1835;
}
}
}
else
{
uint8_t x_1836; 
lean_dec(x_1781);
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1836 = !lean_is_exclusive(x_1806);
if (x_1836 == 0)
{
return x_1806;
}
else
{
lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; 
x_1837 = lean_ctor_get(x_1806, 0);
x_1838 = lean_ctor_get(x_1806, 1);
lean_inc(x_1838);
lean_inc(x_1837);
lean_dec(x_1806);
x_1839 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1839, 0, x_1837);
lean_ctor_set(x_1839, 1, x_1838);
return x_1839;
}
}
block_1803:
{
lean_object* x_1785; lean_object* x_1786; 
lean_inc(x_1755);
x_1785 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1753, x_1783, x_1739, x_1755);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1786 = l_Lean_setEnv___at_Lean_Meta_mkAuxDefinition___spec__2(x_1785, x_3, x_4, x_5, x_6, x_1784);
if (lean_obj_tag(x_1786) == 0)
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; 
x_1787 = lean_ctor_get(x_1786, 1);
lean_inc(x_1787);
lean_dec(x_1786);
x_1788 = lean_box(0);
x_1789 = l_Lean_mkConst(x_1755, x_1788);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1789);
x_1790 = l_Lean_Meta_inferType(x_1789, x_3, x_4, x_5, x_6, x_1787);
if (lean_obj_tag(x_1790) == 0)
{
lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; 
x_1791 = lean_ctor_get(x_1790, 0);
lean_inc(x_1791);
x_1792 = lean_ctor_get(x_1790, 1);
lean_inc(x_1792);
lean_dec(x_1790);
x_1793 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed), 11, 4);
lean_closure_set(x_1793, 0, x_1);
lean_closure_set(x_1793, 1, x_1760);
lean_closure_set(x_1793, 2, x_1746);
lean_closure_set(x_1793, 3, x_1789);
x_1794 = l_Lean_Meta_forallTelescope___rarg(x_1791, x_1793, x_3, x_4, x_5, x_6, x_1792);
return x_1794;
}
else
{
uint8_t x_1795; 
lean_dec(x_1789);
lean_dec(x_1746);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1795 = !lean_is_exclusive(x_1790);
if (x_1795 == 0)
{
return x_1790;
}
else
{
lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; 
x_1796 = lean_ctor_get(x_1790, 0);
x_1797 = lean_ctor_get(x_1790, 1);
lean_inc(x_1797);
lean_inc(x_1796);
lean_dec(x_1790);
x_1798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1798, 0, x_1796);
lean_ctor_set(x_1798, 1, x_1797);
return x_1798;
}
}
}
else
{
uint8_t x_1799; 
lean_dec(x_1755);
lean_dec(x_1746);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1799 = !lean_is_exclusive(x_1786);
if (x_1799 == 0)
{
return x_1786;
}
else
{
lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; 
x_1800 = lean_ctor_get(x_1786, 0);
x_1801 = lean_ctor_get(x_1786, 1);
lean_inc(x_1801);
lean_inc(x_1800);
lean_dec(x_1786);
x_1802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1802, 0, x_1800);
lean_ctor_set(x_1802, 1, x_1801);
return x_1802;
}
}
}
}
else
{
uint8_t x_1840; 
lean_dec(x_1759);
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1840 = !lean_is_exclusive(x_1780);
if (x_1840 == 0)
{
return x_1780;
}
else
{
lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; 
x_1841 = lean_ctor_get(x_1780, 0);
x_1842 = lean_ctor_get(x_1780, 1);
lean_inc(x_1842);
lean_inc(x_1841);
lean_dec(x_1780);
x_1843 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1843, 0, x_1841);
lean_ctor_set(x_1843, 1, x_1842);
return x_1843;
}
}
}
}
}
else
{
uint8_t x_1873; 
lean_dec(x_1759);
lean_dec(x_1757);
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1752);
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1873 = !lean_is_exclusive(x_1761);
if (x_1873 == 0)
{
return x_1761;
}
else
{
lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; 
x_1874 = lean_ctor_get(x_1761, 0);
x_1875 = lean_ctor_get(x_1761, 1);
lean_inc(x_1875);
lean_inc(x_1874);
lean_dec(x_1761);
x_1876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1876, 0, x_1874);
lean_ctor_set(x_1876, 1, x_1875);
return x_1876;
}
}
}
else
{
uint8_t x_1877; 
lean_dec(x_1755);
lean_dec(x_1753);
lean_dec(x_1752);
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1877 = !lean_is_exclusive(x_1756);
if (x_1877 == 0)
{
return x_1756;
}
else
{
lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; 
x_1878 = lean_ctor_get(x_1756, 0);
x_1879 = lean_ctor_get(x_1756, 1);
lean_inc(x_1879);
lean_inc(x_1878);
lean_dec(x_1756);
x_1880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1880, 0, x_1878);
lean_ctor_set(x_1880, 1, x_1879);
return x_1880;
}
}
}
else
{
lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; 
lean_dec(x_1753);
lean_dec(x_1752);
lean_dec(x_1748);
lean_dec(x_1739);
lean_dec(x_9);
x_1881 = lean_ctor_get(x_1754, 0);
lean_inc(x_1881);
lean_dec(x_1754);
x_1882 = lean_box(0);
x_1883 = l_Lean_mkConst(x_1881, x_1882);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1883);
x_1884 = l_Lean_Meta_inferType(x_1883, x_3, x_4, x_5, x_6, x_1751);
if (lean_obj_tag(x_1884) == 0)
{
lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; 
x_1885 = lean_ctor_get(x_1884, 0);
lean_inc(x_1885);
x_1886 = lean_ctor_get(x_1884, 1);
lean_inc(x_1886);
lean_dec(x_1884);
x_1887 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed), 10, 3);
lean_closure_set(x_1887, 0, x_1);
lean_closure_set(x_1887, 1, x_1746);
lean_closure_set(x_1887, 2, x_1883);
x_1888 = l_Lean_Meta_forallTelescope___rarg(x_1885, x_1887, x_3, x_4, x_5, x_6, x_1886);
return x_1888;
}
else
{
uint8_t x_1889; 
lean_dec(x_1883);
lean_dec(x_1746);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1889 = !lean_is_exclusive(x_1884);
if (x_1889 == 0)
{
return x_1884;
}
else
{
lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; 
x_1890 = lean_ctor_get(x_1884, 0);
x_1891 = lean_ctor_get(x_1884, 1);
lean_inc(x_1891);
lean_inc(x_1890);
lean_dec(x_1884);
x_1892 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1892, 0, x_1890);
lean_ctor_set(x_1892, 1, x_1891);
return x_1892;
}
}
}
}
else
{
uint8_t x_1893; 
lean_dec(x_1748);
lean_dec(x_1746);
lean_dec(x_1739);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1893 = !lean_is_exclusive(x_1749);
if (x_1893 == 0)
{
return x_1749;
}
else
{
lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; 
x_1894 = lean_ctor_get(x_1749, 0);
x_1895 = lean_ctor_get(x_1749, 1);
lean_inc(x_1895);
lean_inc(x_1894);
lean_dec(x_1749);
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
lean_dec(x_1728);
lean_dec(x_1);
x_1897 = lean_box(0);
x_1729 = x_1897;
goto block_1738;
}
block_1738:
{
lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; 
lean_dec(x_1729);
x_1730 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1731 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1731, 0, x_1730);
x_1732 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1732, 0, x_1731);
x_1733 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1734 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1734, 0, x_1733);
lean_ctor_set(x_1734, 1, x_1732);
x_1735 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_1736 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1736, 0, x_1734);
lean_ctor_set(x_1736, 1, x_1735);
x_1737 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1736, x_3, x_4, x_5, x_6, x_1727);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1737;
}
}
}
}
else
{
uint8_t x_1898; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1898 = !lean_is_exclusive(x_8);
if (x_1898 == 0)
{
return x_8;
}
else
{
lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; 
x_1899 = lean_ctor_get(x_8, 0);
x_1900 = lean_ctor_get(x_8, 1);
lean_inc(x_1900);
lean_inc(x_1899);
lean_dec(x_8);
x_1901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1901, 0, x_1899);
lean_ctor_set(x_1901, 1, x_1900);
return x_1901;
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = l_Lean_mkConst(x_2, x_7);
x_9 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_10 = lean_io_mk_ref(x_9, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_1);
x_14 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_8, x_13, x_11, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_io_ref_get(x_11, x_16);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_io_ref_get(x_5, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_mk_syntax_ident(x_2);
x_25 = l_Lean_mkOptionalNode___closed__2;
x_26 = lean_array_push(x_25, x_24);
x_27 = l_Lean_nullKind;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
if (x_3 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = lean_add_attribute(x_23, x_19, x_31, x_28, x_32, x_22);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_34, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 1;
x_47 = lean_add_attribute(x_23, x_19, x_45, x_28, x_46, x_22);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_48, x_4, x_5, x_49);
lean_dec(x_5);
lean_dec(x_4);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
lean_dec(x_17);
x_58 = l_Lean_ParserCompiler_compileParser___rarg___closed__1;
x_59 = l_unreachable_x21___rarg(x_58);
x_60 = lean_apply_3(x_59, x_4, x_5, x_57);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
return x_14;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParser___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___at_Lean_Core_checkRecDepth___spec__1___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___at_Lean_Core_checkRecDepth___spec__1___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___at_Lean_Core_checkRecDepth___spec__1___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_getConstInfo___at_Lean_mkInitAttr___spec__1(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_ref_get(x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_15 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_18 = l_Lean_Expr_isConstOf(x_14, x_17);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_9);
x_19 = lean_eval_const(x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
x_20 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_19, x_3, x_4, x_12);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_4(x_23, x_21, x_3, x_4, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_29, x_13, x_2);
lean_dec(x_13);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_free_object(x_9);
x_31 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_31, x_3, x_4, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_io_ref_get(x_4, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Name_append___main(x_2, x_38);
lean_dec(x_2);
x_40 = lean_eval_const(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_40, x_3, x_4, x_36);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
lean_dec(x_30);
lean_ctor_set(x_9, 0, x_46);
return x_9;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_47, x_13, x_2);
lean_dec(x_13);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; lean_object* x_50; 
lean_free_object(x_9);
x_49 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_49, x_3, x_4, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_io_ref_get(x_4, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = l_Lean_Name_append___main(x_2, x_56);
lean_dec(x_2);
x_58 = lean_eval_const(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
x_59 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_58, x_3, x_4, x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_48, 0);
lean_inc(x_64);
lean_dec(x_48);
lean_ctor_set(x_9, 0, x_64);
return x_9;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_9, 0);
x_66 = lean_ctor_get(x_9, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_9);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_69 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_70 = l_Lean_Expr_isConstOf(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_72 = l_Lean_Expr_isConstOf(x_68, x_71);
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_eval_const(x_67, x_2);
lean_dec(x_2);
lean_dec(x_67);
x_74 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_73, x_3, x_4, x_66);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_1, 3);
lean_inc(x_77);
lean_dec(x_1);
x_78 = lean_apply_4(x_77, x_75, x_3, x_4, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
x_84 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_83, x_67, x_2);
lean_dec(x_67);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; lean_object* x_86; 
x_85 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_86 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_85, x_3, x_4, x_66);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_io_ref_get(x_4, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
lean_dec(x_1);
x_93 = l_Lean_Name_append___main(x_2, x_92);
lean_dec(x_2);
x_94 = lean_eval_const(x_91, x_93);
lean_dec(x_93);
lean_dec(x_91);
x_95 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_94, x_3, x_4, x_90);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_98 = x_86;
} else {
 lean_dec_ref(x_86);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
lean_dec(x_84);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_66);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_68);
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
x_103 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_102, x_67, x_2);
lean_dec(x_67);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; lean_object* x_105; 
x_104 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_105 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_104, x_3, x_4, x_66);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_io_ref_get(x_4, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
lean_dec(x_1);
x_112 = l_Lean_Name_append___main(x_2, x_111);
lean_dec(x_2);
x_113 = lean_eval_const(x_110, x_112);
lean_dec(x_112);
lean_dec(x_110);
x_114 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_113, x_3, x_4, x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_ctor_get(x_105, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_105, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_117 = x_105;
} else {
 lean_dec_ref(x_105);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_103, 0);
lean_inc(x_119);
lean_dec(x_103);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_66);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_6);
if (x_121 == 0)
{
return x_6;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_6, 0);
x_123 = lean_ctor_get(x_6, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_6);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_interpretParser___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_4 == 0)
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_ParserCompiler_interpretParser___rarg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_io_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1), 3, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_9);
x_18 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_16, x_14, x_17);
lean_dec(x_16);
x_19 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_18, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
x_24 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed), 7, 1);
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
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
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
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
