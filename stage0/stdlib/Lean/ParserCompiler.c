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
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
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
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_ECoreM_inhabited___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_setEnv(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_toECoreM___rarg___closed__3;
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
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_getConstInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
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
lean_object* l_Lean_Meta_setEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_getRef___rarg(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Core_Exception_inhabited;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
extern lean_object* l_Lean_Meta_MetaM_toECoreM___rarg___closed__2;
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_30 = l_Lean_Core_getEnv___rarg(x_6, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_34, x_31, x_22);
lean_dec(x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_inc(x_33);
x_36 = l_Lean_Name_append___main(x_22, x_33);
lean_inc(x_22);
x_37 = l_Lean_Meta_getConstInfo(x_22, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_ConstantInfo_type(x_38);
x_41 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_42 = l_Lean_Meta_forallTelescope___rarg(x_40, x_41, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_118; uint8_t x_119; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_118 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_119 = l_Lean_Expr_isConstOf(x_43, x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_121 = l_Lean_Expr_isConstOf(x_43, x_120);
lean_dec(x_43);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_122 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_1);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_125, 0, x_33);
x_126 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Core_getConstInfo___closed__5;
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Meta_throwError___rarg(x_135, x_3, x_4, x_5, x_6, x_124);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_33);
lean_dec(x_9);
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
lean_dec(x_122);
x_138 = lean_ctor_get(x_123, 0);
lean_inc(x_138);
lean_dec(x_123);
x_2 = x_138;
x_7 = x_137;
goto _start;
}
}
else
{
uint8_t x_140; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_122);
if (x_140 == 0)
{
return x_122;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_122, 0);
x_142 = lean_ctor_get(x_122, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_122);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; 
x_144 = lean_box(0);
x_45 = x_144;
goto block_117;
}
}
else
{
lean_object* x_145; 
lean_dec(x_43);
x_145 = lean_box(0);
x_45 = x_145;
goto block_117;
}
block_117:
{
lean_object* x_46; 
lean_dec(x_45);
x_46 = l_Lean_ConstantInfo_value_x3f(x_38);
lean_dec(x_38);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_1);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_33);
x_48 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Core_getConstInfo___closed__5;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_throwError___rarg(x_57, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_33);
lean_dec(x_9);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
lean_dec(x_46);
x_60 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_59);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_61 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_60, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_81 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_82 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed), 9, 2);
lean_closure_set(x_82, 0, x_1);
lean_closure_set(x_82, 1, x_81);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = l_Lean_Meta_forallTelescope___rarg(x_40, x_82, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_box(0);
lean_inc(x_36);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_36);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_84);
x_88 = lean_box(0);
x_89 = 0;
x_90 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_62);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*3, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_Core_getEnv___rarg(x_6, x_85);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Options_empty;
x_96 = l_Lean_Environment_addAndCompile(x_93, x_95, x_91);
lean_dec(x_91);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_1);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_KernelException_toMessageData(x_97, x_95);
x_99 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_98);
x_100 = l_Lean_Format_pretty(x_99, x_95);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_Meta_throwError___rarg(x_102, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_96, 0);
lean_inc(x_108);
lean_dec(x_96);
x_64 = x_108;
x_65 = x_94;
goto block_80;
}
}
else
{
uint8_t x_109; 
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_83);
if (x_109 == 0)
{
return x_83;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_83, 0);
x_111 = lean_ctor_get(x_83, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_83);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
block_80:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_36);
x_66 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_34, x_64, x_22, x_36);
x_67 = l_Lean_Meta_setEnv(x_66, x_3, x_4, x_5, x_6, x_65);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_box(0);
x_70 = l_Lean_mkConst(x_36, x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_70);
x_71 = l_Lean_Meta_inferType(x_70, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed), 11, 4);
lean_closure_set(x_74, 0, x_1);
lean_closure_set(x_74, 1, x_41);
lean_closure_set(x_74, 2, x_29);
lean_closure_set(x_74, 3, x_70);
x_75 = l_Lean_Meta_forallTelescope___rarg(x_72, x_74, x_3, x_4, x_5, x_6, x_73);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_61);
if (x_113 == 0)
{
return x_61;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_61, 0);
x_115 = lean_ctor_get(x_61, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_61);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
return x_42;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_42, 0);
x_148 = lean_ctor_get(x_42, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_42);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_37);
if (x_150 == 0)
{
return x_37;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_37, 0);
x_152 = lean_ctor_get(x_37, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_37);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_9);
x_154 = lean_ctor_get(x_35, 0);
lean_inc(x_154);
lean_dec(x_35);
x_155 = lean_box(0);
x_156 = l_Lean_mkConst(x_154, x_155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_156);
x_157 = l_Lean_Meta_inferType(x_156, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed), 10, 3);
lean_closure_set(x_160, 0, x_1);
lean_closure_set(x_160, 1, x_29);
lean_closure_set(x_160, 2, x_156);
x_161 = l_Lean_Meta_forallTelescope___rarg(x_158, x_160, x_3, x_4, x_5, x_6, x_159);
return x_161;
}
else
{
uint8_t x_162; 
lean_dec(x_156);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_157);
if (x_162 == 0)
{
return x_157;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_157, 0);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_11);
lean_dec(x_1);
x_166 = lean_box(0);
x_12 = x_166;
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
x_18 = l_Lean_Core_getConstInfo___closed__5;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_throwError___rarg(x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
case 1:
{
uint8_t x_167; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_8);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_8, 0);
lean_dec(x_168);
return x_8;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_8, 1);
lean_inc(x_169);
lean_dec(x_8);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_9);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
case 2:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_8, 1);
lean_inc(x_171);
lean_dec(x_8);
x_172 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_172) == 4)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_183 = lean_ctor_get(x_172, 0);
lean_inc(x_183);
lean_dec(x_172);
x_184 = lean_unsigned_to_nat(0u);
x_185 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_184);
x_186 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_185);
x_187 = lean_mk_array(x_185, x_186);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_sub(x_185, x_188);
lean_dec(x_185);
lean_inc(x_9);
x_190 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_187, x_189);
x_191 = l_Lean_Core_getEnv___rarg(x_6, x_171);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_1, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_1, 2);
lean_inc(x_195);
x_196 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_195, x_192, x_183);
lean_dec(x_192);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_inc(x_194);
x_197 = l_Lean_Name_append___main(x_183, x_194);
lean_inc(x_183);
x_198 = l_Lean_Meta_getConstInfo(x_183, x_3, x_4, x_5, x_6, x_193);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_ConstantInfo_type(x_199);
x_202 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_201);
x_203 = l_Lean_Meta_forallTelescope___rarg(x_201, x_202, x_3, x_4, x_5, x_6, x_200);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_279; uint8_t x_280; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_279 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_280 = l_Lean_Expr_isConstOf(x_204, x_279);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_282 = l_Lean_Expr_isConstOf(x_204, x_281);
lean_dec(x_204);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_190);
lean_dec(x_183);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_283 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_1);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_286, 0, x_194);
x_287 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_288 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_290 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_292 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_294, 0, x_290);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_Core_getConstInfo___closed__5;
x_296 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l_Lean_Meta_throwError___rarg(x_296, x_3, x_4, x_5, x_6, x_285);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_194);
lean_dec(x_9);
x_298 = lean_ctor_get(x_283, 1);
lean_inc(x_298);
lean_dec(x_283);
x_299 = lean_ctor_get(x_284, 0);
lean_inc(x_299);
lean_dec(x_284);
x_2 = x_299;
x_7 = x_298;
goto _start;
}
}
else
{
uint8_t x_301; 
lean_dec(x_194);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_283);
if (x_301 == 0)
{
return x_283;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_283, 0);
x_303 = lean_ctor_get(x_283, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_283);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
else
{
lean_object* x_305; 
x_305 = lean_box(0);
x_206 = x_305;
goto block_278;
}
}
else
{
lean_object* x_306; 
lean_dec(x_204);
x_306 = lean_box(0);
x_206 = x_306;
goto block_278;
}
block_278:
{
lean_object* x_207; 
lean_dec(x_206);
x_207 = l_Lean_ConstantInfo_value_x3f(x_199);
lean_dec(x_199);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_201);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_190);
lean_dec(x_183);
lean_dec(x_1);
x_208 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_208, 0, x_194);
x_209 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_210 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_212 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_214 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_Core_getConstInfo___closed__5;
x_218 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_Meta_throwError___rarg(x_218, x_3, x_4, x_5, x_6, x_205);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_194);
lean_dec(x_9);
x_220 = lean_ctor_get(x_207, 0);
lean_inc(x_220);
lean_dec(x_207);
x_221 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_220);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_222 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_221, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_242 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_243 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed), 9, 2);
lean_closure_set(x_243, 0, x_1);
lean_closure_set(x_243, 1, x_242);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_244 = l_Lean_Meta_forallTelescope___rarg(x_201, x_243, x_3, x_4, x_5, x_6, x_224);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_box(0);
lean_inc(x_197);
x_248 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_248, 0, x_197);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_245);
x_249 = lean_box(0);
x_250 = 0;
x_251 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_223);
lean_ctor_set(x_251, 2, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*3, x_250);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_253 = l_Lean_Core_getEnv___rarg(x_6, x_246);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = l_Lean_Options_empty;
x_257 = l_Lean_Environment_addAndCompile(x_254, x_256, x_252);
lean_dec(x_252);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_190);
lean_dec(x_183);
lean_dec(x_1);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_Lean_KernelException_toMessageData(x_258, x_256);
x_260 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_259);
x_261 = l_Lean_Format_pretty(x_260, x_256);
x_262 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_262, 0, x_261);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = l_Lean_Meta_throwError___rarg(x_263, x_3, x_4, x_5, x_6, x_255);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_269; 
x_269 = lean_ctor_get(x_257, 0);
lean_inc(x_269);
lean_dec(x_257);
x_225 = x_269;
x_226 = x_255;
goto block_241;
}
}
else
{
uint8_t x_270; 
lean_dec(x_223);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_190);
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_244);
if (x_270 == 0)
{
return x_244;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_244, 0);
x_272 = lean_ctor_get(x_244, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_244);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
block_241:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_inc(x_197);
x_227 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_195, x_225, x_183, x_197);
x_228 = l_Lean_Meta_setEnv(x_227, x_3, x_4, x_5, x_6, x_226);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_box(0);
x_231 = l_Lean_mkConst(x_197, x_230);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_231);
x_232 = l_Lean_Meta_inferType(x_231, x_3, x_4, x_5, x_6, x_229);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed), 11, 4);
lean_closure_set(x_235, 0, x_1);
lean_closure_set(x_235, 1, x_202);
lean_closure_set(x_235, 2, x_190);
lean_closure_set(x_235, 3, x_231);
x_236 = l_Lean_Meta_forallTelescope___rarg(x_233, x_235, x_3, x_4, x_5, x_6, x_234);
return x_236;
}
else
{
uint8_t x_237; 
lean_dec(x_231);
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_232);
if (x_237 == 0)
{
return x_232;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_232, 0);
x_239 = lean_ctor_get(x_232, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_232);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_201);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_190);
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_222);
if (x_274 == 0)
{
return x_222;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_222, 0);
x_276 = lean_ctor_get(x_222, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_222);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_190);
lean_dec(x_183);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_203);
if (x_307 == 0)
{
return x_203;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_203, 0);
x_309 = lean_ctor_get(x_203, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_203);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_190);
lean_dec(x_183);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_198);
if (x_311 == 0)
{
return x_198;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_198, 0);
x_313 = lean_ctor_get(x_198, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_198);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_183);
lean_dec(x_9);
x_315 = lean_ctor_get(x_196, 0);
lean_inc(x_315);
lean_dec(x_196);
x_316 = lean_box(0);
x_317 = l_Lean_mkConst(x_315, x_316);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_317);
x_318 = l_Lean_Meta_inferType(x_317, x_3, x_4, x_5, x_6, x_193);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed), 10, 3);
lean_closure_set(x_321, 0, x_1);
lean_closure_set(x_321, 1, x_190);
lean_closure_set(x_321, 2, x_317);
x_322 = l_Lean_Meta_forallTelescope___rarg(x_319, x_321, x_3, x_4, x_5, x_6, x_320);
return x_322;
}
else
{
uint8_t x_323; 
lean_dec(x_317);
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_318);
if (x_323 == 0)
{
return x_318;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_318, 0);
x_325 = lean_ctor_get(x_318, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_318);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
else
{
lean_object* x_327; 
lean_dec(x_172);
lean_dec(x_1);
x_327 = lean_box(0);
x_173 = x_327;
goto block_182;
}
block_182:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_173);
x_174 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_178 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = l_Lean_Core_getConstInfo___closed__5;
x_180 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_Meta_throwError___rarg(x_180, x_3, x_4, x_5, x_6, x_171);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_181;
}
}
case 3:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_8, 1);
lean_inc(x_328);
lean_dec(x_8);
x_329 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_329) == 4)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_340 = lean_ctor_get(x_329, 0);
lean_inc(x_340);
lean_dec(x_329);
x_341 = lean_unsigned_to_nat(0u);
x_342 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_341);
x_343 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_342);
x_344 = lean_mk_array(x_342, x_343);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_nat_sub(x_342, x_345);
lean_dec(x_342);
lean_inc(x_9);
x_347 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_344, x_346);
x_348 = l_Lean_Core_getEnv___rarg(x_6, x_328);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_ctor_get(x_1, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_1, 2);
lean_inc(x_352);
x_353 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_352, x_349, x_340);
lean_dec(x_349);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
lean_inc(x_351);
x_354 = l_Lean_Name_append___main(x_340, x_351);
lean_inc(x_340);
x_355 = l_Lean_Meta_getConstInfo(x_340, x_3, x_4, x_5, x_6, x_350);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = l_Lean_ConstantInfo_type(x_356);
x_359 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_358);
x_360 = l_Lean_Meta_forallTelescope___rarg(x_358, x_359, x_3, x_4, x_5, x_6, x_357);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_436; uint8_t x_437; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_436 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_437 = l_Lean_Expr_isConstOf(x_361, x_436);
if (x_437 == 0)
{
lean_object* x_438; uint8_t x_439; 
x_438 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_439 = l_Lean_Expr_isConstOf(x_361, x_438);
lean_dec(x_361);
if (x_439 == 0)
{
lean_object* x_440; 
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_347);
lean_dec(x_340);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_440 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_362);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_1);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_443, 0, x_351);
x_444 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_445 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
x_446 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_447 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_449 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_449, 0, x_448);
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_449);
x_451 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_451, 0, x_447);
lean_ctor_set(x_451, 1, x_450);
x_452 = l_Lean_Core_getConstInfo___closed__5;
x_453 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_Lean_Meta_throwError___rarg(x_453, x_3, x_4, x_5, x_6, x_442);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_351);
lean_dec(x_9);
x_455 = lean_ctor_get(x_440, 1);
lean_inc(x_455);
lean_dec(x_440);
x_456 = lean_ctor_get(x_441, 0);
lean_inc(x_456);
lean_dec(x_441);
x_2 = x_456;
x_7 = x_455;
goto _start;
}
}
else
{
uint8_t x_458; 
lean_dec(x_351);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_458 = !lean_is_exclusive(x_440);
if (x_458 == 0)
{
return x_440;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_440, 0);
x_460 = lean_ctor_get(x_440, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_440);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
else
{
lean_object* x_462; 
x_462 = lean_box(0);
x_363 = x_462;
goto block_435;
}
}
else
{
lean_object* x_463; 
lean_dec(x_361);
x_463 = lean_box(0);
x_363 = x_463;
goto block_435;
}
block_435:
{
lean_object* x_364; 
lean_dec(x_363);
x_364 = l_Lean_ConstantInfo_value_x3f(x_356);
lean_dec(x_356);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_358);
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_347);
lean_dec(x_340);
lean_dec(x_1);
x_365 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_365, 0, x_351);
x_366 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_367 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_369 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_371 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_372 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_372, 0, x_371);
x_373 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_373, 0, x_369);
lean_ctor_set(x_373, 1, x_372);
x_374 = l_Lean_Core_getConstInfo___closed__5;
x_375 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_Meta_throwError___rarg(x_375, x_3, x_4, x_5, x_6, x_362);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_351);
lean_dec(x_9);
x_377 = lean_ctor_get(x_364, 0);
lean_inc(x_377);
lean_dec(x_364);
x_378 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_377);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_379 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_378, x_3, x_4, x_5, x_6, x_362);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_399 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_400 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed), 9, 2);
lean_closure_set(x_400, 0, x_1);
lean_closure_set(x_400, 1, x_399);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_401 = l_Lean_Meta_forallTelescope___rarg(x_358, x_400, x_3, x_4, x_5, x_6, x_381);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_box(0);
lean_inc(x_354);
x_405 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_405, 0, x_354);
lean_ctor_set(x_405, 1, x_404);
lean_ctor_set(x_405, 2, x_402);
x_406 = lean_box(0);
x_407 = 0;
x_408 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_380);
lean_ctor_set(x_408, 2, x_406);
lean_ctor_set_uint8(x_408, sizeof(void*)*3, x_407);
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_408);
x_410 = l_Lean_Core_getEnv___rarg(x_6, x_403);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l_Lean_Options_empty;
x_414 = l_Lean_Environment_addAndCompile(x_411, x_413, x_409);
lean_dec(x_409);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_347);
lean_dec(x_340);
lean_dec(x_1);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
lean_dec(x_414);
x_416 = l_Lean_KernelException_toMessageData(x_415, x_413);
x_417 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_416);
x_418 = l_Lean_Format_pretty(x_417, x_413);
x_419 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_419, 0, x_418);
x_420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_420, 0, x_419);
x_421 = l_Lean_Meta_throwError___rarg(x_420, x_3, x_4, x_5, x_6, x_412);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_422 = !lean_is_exclusive(x_421);
if (x_422 == 0)
{
return x_421;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_421, 0);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_421);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
else
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_414, 0);
lean_inc(x_426);
lean_dec(x_414);
x_382 = x_426;
x_383 = x_412;
goto block_398;
}
}
else
{
uint8_t x_427; 
lean_dec(x_380);
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_347);
lean_dec(x_340);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_427 = !lean_is_exclusive(x_401);
if (x_427 == 0)
{
return x_401;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_401, 0);
x_429 = lean_ctor_get(x_401, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_401);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
block_398:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_inc(x_354);
x_384 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_352, x_382, x_340, x_354);
x_385 = l_Lean_Meta_setEnv(x_384, x_3, x_4, x_5, x_6, x_383);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_box(0);
x_388 = l_Lean_mkConst(x_354, x_387);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_388);
x_389 = l_Lean_Meta_inferType(x_388, x_3, x_4, x_5, x_6, x_386);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed), 11, 4);
lean_closure_set(x_392, 0, x_1);
lean_closure_set(x_392, 1, x_359);
lean_closure_set(x_392, 2, x_347);
lean_closure_set(x_392, 3, x_388);
x_393 = l_Lean_Meta_forallTelescope___rarg(x_390, x_392, x_3, x_4, x_5, x_6, x_391);
return x_393;
}
else
{
uint8_t x_394; 
lean_dec(x_388);
lean_dec(x_347);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_394 = !lean_is_exclusive(x_389);
if (x_394 == 0)
{
return x_389;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_389, 0);
x_396 = lean_ctor_get(x_389, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_389);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
}
else
{
uint8_t x_431; 
lean_dec(x_358);
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_347);
lean_dec(x_340);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_431 = !lean_is_exclusive(x_379);
if (x_431 == 0)
{
return x_379;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_379, 0);
x_433 = lean_ctor_get(x_379, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_379);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
}
}
else
{
uint8_t x_464; 
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_347);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_464 = !lean_is_exclusive(x_360);
if (x_464 == 0)
{
return x_360;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_360, 0);
x_466 = lean_ctor_get(x_360, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_360);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
return x_467;
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_347);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_468 = !lean_is_exclusive(x_355);
if (x_468 == 0)
{
return x_355;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_355, 0);
x_470 = lean_ctor_get(x_355, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_355);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_340);
lean_dec(x_9);
x_472 = lean_ctor_get(x_353, 0);
lean_inc(x_472);
lean_dec(x_353);
x_473 = lean_box(0);
x_474 = l_Lean_mkConst(x_472, x_473);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_474);
x_475 = l_Lean_Meta_inferType(x_474, x_3, x_4, x_5, x_6, x_350);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed), 10, 3);
lean_closure_set(x_478, 0, x_1);
lean_closure_set(x_478, 1, x_347);
lean_closure_set(x_478, 2, x_474);
x_479 = l_Lean_Meta_forallTelescope___rarg(x_476, x_478, x_3, x_4, x_5, x_6, x_477);
return x_479;
}
else
{
uint8_t x_480; 
lean_dec(x_474);
lean_dec(x_347);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_480 = !lean_is_exclusive(x_475);
if (x_480 == 0)
{
return x_475;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_475, 0);
x_482 = lean_ctor_get(x_475, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_475);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
}
else
{
lean_object* x_484; 
lean_dec(x_329);
lean_dec(x_1);
x_484 = lean_box(0);
x_330 = x_484;
goto block_339;
}
block_339:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_330);
x_331 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_332 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
x_334 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_335 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Lean_Core_getConstInfo___closed__5;
x_337 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = l_Lean_Meta_throwError___rarg(x_337, x_3, x_4, x_5, x_6, x_328);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_338;
}
}
case 4:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_8, 1);
lean_inc(x_485);
lean_dec(x_8);
x_486 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_486) == 4)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_497 = lean_ctor_get(x_486, 0);
lean_inc(x_497);
lean_dec(x_486);
x_498 = lean_unsigned_to_nat(0u);
x_499 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_498);
x_500 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_499);
x_501 = lean_mk_array(x_499, x_500);
x_502 = lean_unsigned_to_nat(1u);
x_503 = lean_nat_sub(x_499, x_502);
lean_dec(x_499);
lean_inc(x_9);
x_504 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_501, x_503);
x_505 = l_Lean_Core_getEnv___rarg(x_6, x_485);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_1, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_1, 2);
lean_inc(x_509);
x_510 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_509, x_506, x_497);
lean_dec(x_506);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; 
lean_inc(x_508);
x_511 = l_Lean_Name_append___main(x_497, x_508);
lean_inc(x_497);
x_512 = l_Lean_Meta_getConstInfo(x_497, x_3, x_4, x_5, x_6, x_507);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = l_Lean_ConstantInfo_type(x_513);
x_516 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_515);
x_517 = l_Lean_Meta_forallTelescope___rarg(x_515, x_516, x_3, x_4, x_5, x_6, x_514);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_593; uint8_t x_594; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_593 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_594 = l_Lean_Expr_isConstOf(x_518, x_593);
if (x_594 == 0)
{
lean_object* x_595; uint8_t x_596; 
x_595 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_596 = l_Lean_Expr_isConstOf(x_518, x_595);
lean_dec(x_518);
if (x_596 == 0)
{
lean_object* x_597; 
lean_dec(x_515);
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_497);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_597 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_519);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_1);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
x_600 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_600, 0, x_508);
x_601 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_602 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_600);
x_603 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_604 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
x_605 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_606 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_606, 0, x_605);
x_607 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_607, 0, x_606);
x_608 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_608, 0, x_604);
lean_ctor_set(x_608, 1, x_607);
x_609 = l_Lean_Core_getConstInfo___closed__5;
x_610 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_610, 0, x_608);
lean_ctor_set(x_610, 1, x_609);
x_611 = l_Lean_Meta_throwError___rarg(x_610, x_3, x_4, x_5, x_6, x_599);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_611;
}
else
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_508);
lean_dec(x_9);
x_612 = lean_ctor_get(x_597, 1);
lean_inc(x_612);
lean_dec(x_597);
x_613 = lean_ctor_get(x_598, 0);
lean_inc(x_613);
lean_dec(x_598);
x_2 = x_613;
x_7 = x_612;
goto _start;
}
}
else
{
uint8_t x_615; 
lean_dec(x_508);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_615 = !lean_is_exclusive(x_597);
if (x_615 == 0)
{
return x_597;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_597, 0);
x_617 = lean_ctor_get(x_597, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_597);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
else
{
lean_object* x_619; 
x_619 = lean_box(0);
x_520 = x_619;
goto block_592;
}
}
else
{
lean_object* x_620; 
lean_dec(x_518);
x_620 = lean_box(0);
x_520 = x_620;
goto block_592;
}
block_592:
{
lean_object* x_521; 
lean_dec(x_520);
x_521 = l_Lean_ConstantInfo_value_x3f(x_513);
lean_dec(x_513);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_515);
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_1);
x_522 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_522, 0, x_508);
x_523 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_524 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_522);
x_525 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_526 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
x_527 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_528 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_528, 0, x_527);
x_529 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_529, 0, x_528);
x_530 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_530, 0, x_526);
lean_ctor_set(x_530, 1, x_529);
x_531 = l_Lean_Core_getConstInfo___closed__5;
x_532 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
x_533 = l_Lean_Meta_throwError___rarg(x_532, x_3, x_4, x_5, x_6, x_519);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_533;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_508);
lean_dec(x_9);
x_534 = lean_ctor_get(x_521, 0);
lean_inc(x_534);
lean_dec(x_521);
x_535 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_534);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_536 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_535, x_3, x_4, x_5, x_6, x_519);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_556 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_557 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed), 9, 2);
lean_closure_set(x_557, 0, x_1);
lean_closure_set(x_557, 1, x_556);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_558 = l_Lean_Meta_forallTelescope___rarg(x_515, x_557, x_3, x_4, x_5, x_6, x_538);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_box(0);
lean_inc(x_511);
x_562 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_562, 0, x_511);
lean_ctor_set(x_562, 1, x_561);
lean_ctor_set(x_562, 2, x_559);
x_563 = lean_box(0);
x_564 = 0;
x_565 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_537);
lean_ctor_set(x_565, 2, x_563);
lean_ctor_set_uint8(x_565, sizeof(void*)*3, x_564);
x_566 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_566, 0, x_565);
x_567 = l_Lean_Core_getEnv___rarg(x_6, x_560);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec(x_567);
x_570 = l_Lean_Options_empty;
x_571 = l_Lean_Environment_addAndCompile(x_568, x_570, x_566);
lean_dec(x_566);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_1);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec(x_571);
x_573 = l_Lean_KernelException_toMessageData(x_572, x_570);
x_574 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_573);
x_575 = l_Lean_Format_pretty(x_574, x_570);
x_576 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_576, 0, x_575);
x_577 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_577, 0, x_576);
x_578 = l_Lean_Meta_throwError___rarg(x_577, x_3, x_4, x_5, x_6, x_569);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_579 = !lean_is_exclusive(x_578);
if (x_579 == 0)
{
return x_578;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_578, 0);
x_581 = lean_ctor_get(x_578, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_578);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
else
{
lean_object* x_583; 
x_583 = lean_ctor_get(x_571, 0);
lean_inc(x_583);
lean_dec(x_571);
x_539 = x_583;
x_540 = x_569;
goto block_555;
}
}
else
{
uint8_t x_584; 
lean_dec(x_537);
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_558);
if (x_584 == 0)
{
return x_558;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_558, 0);
x_586 = lean_ctor_get(x_558, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_558);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
block_555:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_inc(x_511);
x_541 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_509, x_539, x_497, x_511);
x_542 = l_Lean_Meta_setEnv(x_541, x_3, x_4, x_5, x_6, x_540);
x_543 = lean_ctor_get(x_542, 1);
lean_inc(x_543);
lean_dec(x_542);
x_544 = lean_box(0);
x_545 = l_Lean_mkConst(x_511, x_544);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_545);
x_546 = l_Lean_Meta_inferType(x_545, x_3, x_4, x_5, x_6, x_543);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed), 11, 4);
lean_closure_set(x_549, 0, x_1);
lean_closure_set(x_549, 1, x_516);
lean_closure_set(x_549, 2, x_504);
lean_closure_set(x_549, 3, x_545);
x_550 = l_Lean_Meta_forallTelescope___rarg(x_547, x_549, x_3, x_4, x_5, x_6, x_548);
return x_550;
}
else
{
uint8_t x_551; 
lean_dec(x_545);
lean_dec(x_504);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_551 = !lean_is_exclusive(x_546);
if (x_551 == 0)
{
return x_546;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_546, 0);
x_553 = lean_ctor_get(x_546, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_546);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
}
else
{
uint8_t x_588; 
lean_dec(x_515);
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_588 = !lean_is_exclusive(x_536);
if (x_588 == 0)
{
return x_536;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_536, 0);
x_590 = lean_ctor_get(x_536, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_536);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
}
}
else
{
uint8_t x_621; 
lean_dec(x_515);
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_621 = !lean_is_exclusive(x_517);
if (x_621 == 0)
{
return x_517;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_517, 0);
x_623 = lean_ctor_get(x_517, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_517);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
return x_624;
}
}
}
else
{
uint8_t x_625; 
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_625 = !lean_is_exclusive(x_512);
if (x_625 == 0)
{
return x_512;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_512, 0);
x_627 = lean_ctor_get(x_512, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_512);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
return x_628;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_497);
lean_dec(x_9);
x_629 = lean_ctor_get(x_510, 0);
lean_inc(x_629);
lean_dec(x_510);
x_630 = lean_box(0);
x_631 = l_Lean_mkConst(x_629, x_630);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_631);
x_632 = l_Lean_Meta_inferType(x_631, x_3, x_4, x_5, x_6, x_507);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed), 10, 3);
lean_closure_set(x_635, 0, x_1);
lean_closure_set(x_635, 1, x_504);
lean_closure_set(x_635, 2, x_631);
x_636 = l_Lean_Meta_forallTelescope___rarg(x_633, x_635, x_3, x_4, x_5, x_6, x_634);
return x_636;
}
else
{
uint8_t x_637; 
lean_dec(x_631);
lean_dec(x_504);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_632);
if (x_637 == 0)
{
return x_632;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_632, 0);
x_639 = lean_ctor_get(x_632, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_632);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
}
else
{
lean_object* x_641; 
lean_dec(x_486);
lean_dec(x_1);
x_641 = lean_box(0);
x_487 = x_641;
goto block_496;
}
block_496:
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_487);
x_488 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_489 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_489, 0, x_488);
x_490 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_490, 0, x_489);
x_491 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_492 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_490);
x_493 = l_Lean_Core_getConstInfo___closed__5;
x_494 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
x_495 = l_Lean_Meta_throwError___rarg(x_494, x_3, x_4, x_5, x_6, x_485);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_495;
}
}
case 5:
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_8, 1);
lean_inc(x_642);
lean_dec(x_8);
x_643 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_643) == 4)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_654 = lean_ctor_get(x_643, 0);
lean_inc(x_654);
lean_dec(x_643);
x_655 = lean_unsigned_to_nat(0u);
x_656 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_655);
x_657 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_656);
x_658 = lean_mk_array(x_656, x_657);
x_659 = lean_unsigned_to_nat(1u);
x_660 = lean_nat_sub(x_656, x_659);
lean_dec(x_656);
lean_inc(x_9);
x_661 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_658, x_660);
x_662 = l_Lean_Core_getEnv___rarg(x_6, x_642);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = lean_ctor_get(x_1, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_1, 2);
lean_inc(x_666);
x_667 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_666, x_663, x_654);
lean_dec(x_663);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; 
lean_inc(x_665);
x_668 = l_Lean_Name_append___main(x_654, x_665);
lean_inc(x_654);
x_669 = l_Lean_Meta_getConstInfo(x_654, x_3, x_4, x_5, x_6, x_664);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_672 = l_Lean_ConstantInfo_type(x_670);
x_673 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_672);
x_674 = l_Lean_Meta_forallTelescope___rarg(x_672, x_673, x_3, x_4, x_5, x_6, x_671);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_750; uint8_t x_751; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_750 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_751 = l_Lean_Expr_isConstOf(x_675, x_750);
if (x_751 == 0)
{
lean_object* x_752; uint8_t x_753; 
x_752 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_753 = l_Lean_Expr_isConstOf(x_675, x_752);
lean_dec(x_675);
if (x_753 == 0)
{
lean_object* x_754; 
lean_dec(x_672);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_661);
lean_dec(x_654);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_754 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_676);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; 
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_1);
x_756 = lean_ctor_get(x_754, 1);
lean_inc(x_756);
lean_dec(x_754);
x_757 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_757, 0, x_665);
x_758 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_759 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_760 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_761 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
x_762 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_763 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_763, 0, x_762);
x_764 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_764, 0, x_763);
x_765 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_765, 0, x_761);
lean_ctor_set(x_765, 1, x_764);
x_766 = l_Lean_Core_getConstInfo___closed__5;
x_767 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_766);
x_768 = l_Lean_Meta_throwError___rarg(x_767, x_3, x_4, x_5, x_6, x_756);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; 
lean_dec(x_665);
lean_dec(x_9);
x_769 = lean_ctor_get(x_754, 1);
lean_inc(x_769);
lean_dec(x_754);
x_770 = lean_ctor_get(x_755, 0);
lean_inc(x_770);
lean_dec(x_755);
x_2 = x_770;
x_7 = x_769;
goto _start;
}
}
else
{
uint8_t x_772; 
lean_dec(x_665);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_772 = !lean_is_exclusive(x_754);
if (x_772 == 0)
{
return x_754;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_773 = lean_ctor_get(x_754, 0);
x_774 = lean_ctor_get(x_754, 1);
lean_inc(x_774);
lean_inc(x_773);
lean_dec(x_754);
x_775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_775, 0, x_773);
lean_ctor_set(x_775, 1, x_774);
return x_775;
}
}
}
else
{
lean_object* x_776; 
x_776 = lean_box(0);
x_677 = x_776;
goto block_749;
}
}
else
{
lean_object* x_777; 
lean_dec(x_675);
x_777 = lean_box(0);
x_677 = x_777;
goto block_749;
}
block_749:
{
lean_object* x_678; 
lean_dec(x_677);
x_678 = l_Lean_ConstantInfo_value_x3f(x_670);
lean_dec(x_670);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_672);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_661);
lean_dec(x_654);
lean_dec(x_1);
x_679 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_679, 0, x_665);
x_680 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_681 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_679);
x_682 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_683 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
x_684 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_685 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_685, 0, x_684);
x_686 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_686, 0, x_685);
x_687 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_687, 0, x_683);
lean_ctor_set(x_687, 1, x_686);
x_688 = l_Lean_Core_getConstInfo___closed__5;
x_689 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
x_690 = l_Lean_Meta_throwError___rarg(x_689, x_3, x_4, x_5, x_6, x_676);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_690;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_665);
lean_dec(x_9);
x_691 = lean_ctor_get(x_678, 0);
lean_inc(x_691);
lean_dec(x_678);
x_692 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_691);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_693 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_692, x_3, x_4, x_5, x_6, x_676);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_713 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_714 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed), 9, 2);
lean_closure_set(x_714, 0, x_1);
lean_closure_set(x_714, 1, x_713);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_715 = l_Lean_Meta_forallTelescope___rarg(x_672, x_714, x_3, x_4, x_5, x_6, x_695);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_box(0);
lean_inc(x_668);
x_719 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_719, 0, x_668);
lean_ctor_set(x_719, 1, x_718);
lean_ctor_set(x_719, 2, x_716);
x_720 = lean_box(0);
x_721 = 0;
x_722 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_722, 0, x_719);
lean_ctor_set(x_722, 1, x_694);
lean_ctor_set(x_722, 2, x_720);
lean_ctor_set_uint8(x_722, sizeof(void*)*3, x_721);
x_723 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_723, 0, x_722);
x_724 = l_Lean_Core_getEnv___rarg(x_6, x_717);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = l_Lean_Options_empty;
x_728 = l_Lean_Environment_addAndCompile(x_725, x_727, x_723);
lean_dec(x_723);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; 
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_661);
lean_dec(x_654);
lean_dec(x_1);
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
lean_dec(x_728);
x_730 = l_Lean_KernelException_toMessageData(x_729, x_727);
x_731 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_730);
x_732 = l_Lean_Format_pretty(x_731, x_727);
x_733 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_733, 0, x_732);
x_734 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_734, 0, x_733);
x_735 = l_Lean_Meta_throwError___rarg(x_734, x_3, x_4, x_5, x_6, x_726);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_736 = !lean_is_exclusive(x_735);
if (x_736 == 0)
{
return x_735;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_735, 0);
x_738 = lean_ctor_get(x_735, 1);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_735);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
return x_739;
}
}
else
{
lean_object* x_740; 
x_740 = lean_ctor_get(x_728, 0);
lean_inc(x_740);
lean_dec(x_728);
x_696 = x_740;
x_697 = x_726;
goto block_712;
}
}
else
{
uint8_t x_741; 
lean_dec(x_694);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_661);
lean_dec(x_654);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_741 = !lean_is_exclusive(x_715);
if (x_741 == 0)
{
return x_715;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_715, 0);
x_743 = lean_ctor_get(x_715, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_715);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
block_712:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_inc(x_668);
x_698 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_666, x_696, x_654, x_668);
x_699 = l_Lean_Meta_setEnv(x_698, x_3, x_4, x_5, x_6, x_697);
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec(x_699);
x_701 = lean_box(0);
x_702 = l_Lean_mkConst(x_668, x_701);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_702);
x_703 = l_Lean_Meta_inferType(x_702, x_3, x_4, x_5, x_6, x_700);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed), 11, 4);
lean_closure_set(x_706, 0, x_1);
lean_closure_set(x_706, 1, x_673);
lean_closure_set(x_706, 2, x_661);
lean_closure_set(x_706, 3, x_702);
x_707 = l_Lean_Meta_forallTelescope___rarg(x_704, x_706, x_3, x_4, x_5, x_6, x_705);
return x_707;
}
else
{
uint8_t x_708; 
lean_dec(x_702);
lean_dec(x_661);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_708 = !lean_is_exclusive(x_703);
if (x_708 == 0)
{
return x_703;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_703, 0);
x_710 = lean_ctor_get(x_703, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_703);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_672);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_661);
lean_dec(x_654);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_693);
if (x_745 == 0)
{
return x_693;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_693, 0);
x_747 = lean_ctor_get(x_693, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_693);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
}
}
else
{
uint8_t x_778; 
lean_dec(x_672);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_661);
lean_dec(x_654);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_778 = !lean_is_exclusive(x_674);
if (x_778 == 0)
{
return x_674;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_674, 0);
x_780 = lean_ctor_get(x_674, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_674);
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_779);
lean_ctor_set(x_781, 1, x_780);
return x_781;
}
}
}
else
{
uint8_t x_782; 
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_661);
lean_dec(x_654);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_782 = !lean_is_exclusive(x_669);
if (x_782 == 0)
{
return x_669;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_669, 0);
x_784 = lean_ctor_get(x_669, 1);
lean_inc(x_784);
lean_inc(x_783);
lean_dec(x_669);
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_784);
return x_785;
}
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_654);
lean_dec(x_9);
x_786 = lean_ctor_get(x_667, 0);
lean_inc(x_786);
lean_dec(x_667);
x_787 = lean_box(0);
x_788 = l_Lean_mkConst(x_786, x_787);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_788);
x_789 = l_Lean_Meta_inferType(x_788, x_3, x_4, x_5, x_6, x_664);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed), 10, 3);
lean_closure_set(x_792, 0, x_1);
lean_closure_set(x_792, 1, x_661);
lean_closure_set(x_792, 2, x_788);
x_793 = l_Lean_Meta_forallTelescope___rarg(x_790, x_792, x_3, x_4, x_5, x_6, x_791);
return x_793;
}
else
{
uint8_t x_794; 
lean_dec(x_788);
lean_dec(x_661);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_794 = !lean_is_exclusive(x_789);
if (x_794 == 0)
{
return x_789;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_789, 0);
x_796 = lean_ctor_get(x_789, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_789);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
}
}
}
}
else
{
lean_object* x_798; 
lean_dec(x_643);
lean_dec(x_1);
x_798 = lean_box(0);
x_644 = x_798;
goto block_653;
}
block_653:
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_644);
x_645 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_646 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_646, 0, x_645);
x_647 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_647, 0, x_646);
x_648 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_649 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_647);
x_650 = l_Lean_Core_getConstInfo___closed__5;
x_651 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
x_652 = l_Lean_Meta_throwError___rarg(x_651, x_3, x_4, x_5, x_6, x_642);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_652;
}
}
case 6:
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_8, 1);
lean_inc(x_799);
lean_dec(x_8);
x_800 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16), 8, 1);
lean_closure_set(x_800, 0, x_1);
x_801 = l_Lean_Meta_lambdaTelescope___rarg(x_9, x_800, x_3, x_4, x_5, x_6, x_799);
return x_801;
}
case 7:
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_8, 1);
lean_inc(x_802);
lean_dec(x_8);
x_803 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_803) == 4)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_814 = lean_ctor_get(x_803, 0);
lean_inc(x_814);
lean_dec(x_803);
x_815 = lean_unsigned_to_nat(0u);
x_816 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_815);
x_817 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_816);
x_818 = lean_mk_array(x_816, x_817);
x_819 = lean_unsigned_to_nat(1u);
x_820 = lean_nat_sub(x_816, x_819);
lean_dec(x_816);
lean_inc(x_9);
x_821 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_818, x_820);
x_822 = l_Lean_Core_getEnv___rarg(x_6, x_802);
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = lean_ctor_get(x_1, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_1, 2);
lean_inc(x_826);
x_827 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_826, x_823, x_814);
lean_dec(x_823);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; 
lean_inc(x_825);
x_828 = l_Lean_Name_append___main(x_814, x_825);
lean_inc(x_814);
x_829 = l_Lean_Meta_getConstInfo(x_814, x_3, x_4, x_5, x_6, x_824);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_832 = l_Lean_ConstantInfo_type(x_830);
x_833 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_832);
x_834 = l_Lean_Meta_forallTelescope___rarg(x_832, x_833, x_3, x_4, x_5, x_6, x_831);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_910; uint8_t x_911; 
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
lean_dec(x_834);
x_910 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_911 = l_Lean_Expr_isConstOf(x_835, x_910);
if (x_911 == 0)
{
lean_object* x_912; uint8_t x_913; 
x_912 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_913 = l_Lean_Expr_isConstOf(x_835, x_912);
lean_dec(x_835);
if (x_913 == 0)
{
lean_object* x_914; 
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_821);
lean_dec(x_814);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_914 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_836);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; 
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_1);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
x_917 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_917, 0, x_825);
x_918 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_919 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_917);
x_920 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_921 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
x_922 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_923 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_923, 0, x_922);
x_924 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_924, 0, x_923);
x_925 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_925, 0, x_921);
lean_ctor_set(x_925, 1, x_924);
x_926 = l_Lean_Core_getConstInfo___closed__5;
x_927 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_927, 0, x_925);
lean_ctor_set(x_927, 1, x_926);
x_928 = l_Lean_Meta_throwError___rarg(x_927, x_3, x_4, x_5, x_6, x_916);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_928;
}
else
{
lean_object* x_929; lean_object* x_930; 
lean_dec(x_825);
lean_dec(x_9);
x_929 = lean_ctor_get(x_914, 1);
lean_inc(x_929);
lean_dec(x_914);
x_930 = lean_ctor_get(x_915, 0);
lean_inc(x_930);
lean_dec(x_915);
x_2 = x_930;
x_7 = x_929;
goto _start;
}
}
else
{
uint8_t x_932; 
lean_dec(x_825);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_932 = !lean_is_exclusive(x_914);
if (x_932 == 0)
{
return x_914;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_914, 0);
x_934 = lean_ctor_get(x_914, 1);
lean_inc(x_934);
lean_inc(x_933);
lean_dec(x_914);
x_935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_934);
return x_935;
}
}
}
else
{
lean_object* x_936; 
x_936 = lean_box(0);
x_837 = x_936;
goto block_909;
}
}
else
{
lean_object* x_937; 
lean_dec(x_835);
x_937 = lean_box(0);
x_837 = x_937;
goto block_909;
}
block_909:
{
lean_object* x_838; 
lean_dec(x_837);
x_838 = l_Lean_ConstantInfo_value_x3f(x_830);
lean_dec(x_830);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_832);
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_821);
lean_dec(x_814);
lean_dec(x_1);
x_839 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_839, 0, x_825);
x_840 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_841 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_839);
x_842 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_843 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_843, 0, x_841);
lean_ctor_set(x_843, 1, x_842);
x_844 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_845 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_845, 0, x_844);
x_846 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_846, 0, x_845);
x_847 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_847, 0, x_843);
lean_ctor_set(x_847, 1, x_846);
x_848 = l_Lean_Core_getConstInfo___closed__5;
x_849 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_848);
x_850 = l_Lean_Meta_throwError___rarg(x_849, x_3, x_4, x_5, x_6, x_836);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_850;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
lean_dec(x_825);
lean_dec(x_9);
x_851 = lean_ctor_get(x_838, 0);
lean_inc(x_851);
lean_dec(x_838);
x_852 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_851);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_853 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_852, x_3, x_4, x_5, x_6, x_836);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
x_873 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_874 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed), 9, 2);
lean_closure_set(x_874, 0, x_1);
lean_closure_set(x_874, 1, x_873);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_875 = l_Lean_Meta_forallTelescope___rarg(x_832, x_874, x_3, x_4, x_5, x_6, x_855);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; uint8_t x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = lean_box(0);
lean_inc(x_828);
x_879 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_879, 0, x_828);
lean_ctor_set(x_879, 1, x_878);
lean_ctor_set(x_879, 2, x_876);
x_880 = lean_box(0);
x_881 = 0;
x_882 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_882, 0, x_879);
lean_ctor_set(x_882, 1, x_854);
lean_ctor_set(x_882, 2, x_880);
lean_ctor_set_uint8(x_882, sizeof(void*)*3, x_881);
x_883 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_883, 0, x_882);
x_884 = l_Lean_Core_getEnv___rarg(x_6, x_877);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = l_Lean_Options_empty;
x_888 = l_Lean_Environment_addAndCompile(x_885, x_887, x_883);
lean_dec(x_883);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; uint8_t x_896; 
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_821);
lean_dec(x_814);
lean_dec(x_1);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
lean_dec(x_888);
x_890 = l_Lean_KernelException_toMessageData(x_889, x_887);
x_891 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_890);
x_892 = l_Lean_Format_pretty(x_891, x_887);
x_893 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_893, 0, x_892);
x_894 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_894, 0, x_893);
x_895 = l_Lean_Meta_throwError___rarg(x_894, x_3, x_4, x_5, x_6, x_886);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_896 = !lean_is_exclusive(x_895);
if (x_896 == 0)
{
return x_895;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_895, 0);
x_898 = lean_ctor_get(x_895, 1);
lean_inc(x_898);
lean_inc(x_897);
lean_dec(x_895);
x_899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_899, 0, x_897);
lean_ctor_set(x_899, 1, x_898);
return x_899;
}
}
else
{
lean_object* x_900; 
x_900 = lean_ctor_get(x_888, 0);
lean_inc(x_900);
lean_dec(x_888);
x_856 = x_900;
x_857 = x_886;
goto block_872;
}
}
else
{
uint8_t x_901; 
lean_dec(x_854);
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_821);
lean_dec(x_814);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_901 = !lean_is_exclusive(x_875);
if (x_901 == 0)
{
return x_875;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_875, 0);
x_903 = lean_ctor_get(x_875, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_875);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
block_872:
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_inc(x_828);
x_858 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_826, x_856, x_814, x_828);
x_859 = l_Lean_Meta_setEnv(x_858, x_3, x_4, x_5, x_6, x_857);
x_860 = lean_ctor_get(x_859, 1);
lean_inc(x_860);
lean_dec(x_859);
x_861 = lean_box(0);
x_862 = l_Lean_mkConst(x_828, x_861);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_862);
x_863 = l_Lean_Meta_inferType(x_862, x_3, x_4, x_5, x_6, x_860);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_863, 1);
lean_inc(x_865);
lean_dec(x_863);
x_866 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed), 11, 4);
lean_closure_set(x_866, 0, x_1);
lean_closure_set(x_866, 1, x_833);
lean_closure_set(x_866, 2, x_821);
lean_closure_set(x_866, 3, x_862);
x_867 = l_Lean_Meta_forallTelescope___rarg(x_864, x_866, x_3, x_4, x_5, x_6, x_865);
return x_867;
}
else
{
uint8_t x_868; 
lean_dec(x_862);
lean_dec(x_821);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_868 = !lean_is_exclusive(x_863);
if (x_868 == 0)
{
return x_863;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_869 = lean_ctor_get(x_863, 0);
x_870 = lean_ctor_get(x_863, 1);
lean_inc(x_870);
lean_inc(x_869);
lean_dec(x_863);
x_871 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_871, 0, x_869);
lean_ctor_set(x_871, 1, x_870);
return x_871;
}
}
}
}
else
{
uint8_t x_905; 
lean_dec(x_832);
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_821);
lean_dec(x_814);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_905 = !lean_is_exclusive(x_853);
if (x_905 == 0)
{
return x_853;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_906 = lean_ctor_get(x_853, 0);
x_907 = lean_ctor_get(x_853, 1);
lean_inc(x_907);
lean_inc(x_906);
lean_dec(x_853);
x_908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_908, 0, x_906);
lean_ctor_set(x_908, 1, x_907);
return x_908;
}
}
}
}
}
else
{
uint8_t x_938; 
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_821);
lean_dec(x_814);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_938 = !lean_is_exclusive(x_834);
if (x_938 == 0)
{
return x_834;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_939 = lean_ctor_get(x_834, 0);
x_940 = lean_ctor_get(x_834, 1);
lean_inc(x_940);
lean_inc(x_939);
lean_dec(x_834);
x_941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
return x_941;
}
}
}
else
{
uint8_t x_942; 
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_821);
lean_dec(x_814);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_942 = !lean_is_exclusive(x_829);
if (x_942 == 0)
{
return x_829;
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_829, 0);
x_944 = lean_ctor_get(x_829, 1);
lean_inc(x_944);
lean_inc(x_943);
lean_dec(x_829);
x_945 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_945, 0, x_943);
lean_ctor_set(x_945, 1, x_944);
return x_945;
}
}
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_814);
lean_dec(x_9);
x_946 = lean_ctor_get(x_827, 0);
lean_inc(x_946);
lean_dec(x_827);
x_947 = lean_box(0);
x_948 = l_Lean_mkConst(x_946, x_947);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_948);
x_949 = l_Lean_Meta_inferType(x_948, x_3, x_4, x_5, x_6, x_824);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
lean_dec(x_949);
x_952 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed), 10, 3);
lean_closure_set(x_952, 0, x_1);
lean_closure_set(x_952, 1, x_821);
lean_closure_set(x_952, 2, x_948);
x_953 = l_Lean_Meta_forallTelescope___rarg(x_950, x_952, x_3, x_4, x_5, x_6, x_951);
return x_953;
}
else
{
uint8_t x_954; 
lean_dec(x_948);
lean_dec(x_821);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_954 = !lean_is_exclusive(x_949);
if (x_954 == 0)
{
return x_949;
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_955 = lean_ctor_get(x_949, 0);
x_956 = lean_ctor_get(x_949, 1);
lean_inc(x_956);
lean_inc(x_955);
lean_dec(x_949);
x_957 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_957, 0, x_955);
lean_ctor_set(x_957, 1, x_956);
return x_957;
}
}
}
}
else
{
lean_object* x_958; 
lean_dec(x_803);
lean_dec(x_1);
x_958 = lean_box(0);
x_804 = x_958;
goto block_813;
}
block_813:
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_804);
x_805 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_806 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_806, 0, x_805);
x_807 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_807, 0, x_806);
x_808 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_809 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_807);
x_810 = l_Lean_Core_getConstInfo___closed__5;
x_811 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
x_812 = l_Lean_Meta_throwError___rarg(x_811, x_3, x_4, x_5, x_6, x_802);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_812;
}
}
case 8:
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_8, 1);
lean_inc(x_959);
lean_dec(x_8);
x_960 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_960) == 4)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_971 = lean_ctor_get(x_960, 0);
lean_inc(x_971);
lean_dec(x_960);
x_972 = lean_unsigned_to_nat(0u);
x_973 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_972);
x_974 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_973);
x_975 = lean_mk_array(x_973, x_974);
x_976 = lean_unsigned_to_nat(1u);
x_977 = lean_nat_sub(x_973, x_976);
lean_dec(x_973);
lean_inc(x_9);
x_978 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_975, x_977);
x_979 = l_Lean_Core_getEnv___rarg(x_6, x_959);
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_979, 1);
lean_inc(x_981);
lean_dec(x_979);
x_982 = lean_ctor_get(x_1, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_1, 2);
lean_inc(x_983);
x_984 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_983, x_980, x_971);
lean_dec(x_980);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; 
lean_inc(x_982);
x_985 = l_Lean_Name_append___main(x_971, x_982);
lean_inc(x_971);
x_986 = l_Lean_Meta_getConstInfo(x_971, x_3, x_4, x_5, x_6, x_981);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
lean_dec(x_986);
x_989 = l_Lean_ConstantInfo_type(x_987);
x_990 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_989);
x_991 = l_Lean_Meta_forallTelescope___rarg(x_989, x_990, x_3, x_4, x_5, x_6, x_988);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_1067; uint8_t x_1068; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec(x_991);
x_1067 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1068 = l_Lean_Expr_isConstOf(x_992, x_1067);
if (x_1068 == 0)
{
lean_object* x_1069; uint8_t x_1070; 
x_1069 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1070 = l_Lean_Expr_isConstOf(x_992, x_1069);
lean_dec(x_992);
if (x_1070 == 0)
{
lean_object* x_1071; 
lean_dec(x_989);
lean_dec(x_987);
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_978);
lean_dec(x_971);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1071 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_993);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
lean_dec(x_1);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
x_1074 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1074, 0, x_982);
x_1075 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1076 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1076, 0, x_1075);
lean_ctor_set(x_1076, 1, x_1074);
x_1077 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1078 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1078, 0, x_1076);
lean_ctor_set(x_1078, 1, x_1077);
x_1079 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1080 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1080, 0, x_1079);
x_1081 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1081, 0, x_1080);
x_1082 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1082, 0, x_1078);
lean_ctor_set(x_1082, 1, x_1081);
x_1083 = l_Lean_Core_getConstInfo___closed__5;
x_1084 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1084, 0, x_1082);
lean_ctor_set(x_1084, 1, x_1083);
x_1085 = l_Lean_Meta_throwError___rarg(x_1084, x_3, x_4, x_5, x_6, x_1073);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1085;
}
else
{
lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_982);
lean_dec(x_9);
x_1086 = lean_ctor_get(x_1071, 1);
lean_inc(x_1086);
lean_dec(x_1071);
x_1087 = lean_ctor_get(x_1072, 0);
lean_inc(x_1087);
lean_dec(x_1072);
x_2 = x_1087;
x_7 = x_1086;
goto _start;
}
}
else
{
uint8_t x_1089; 
lean_dec(x_982);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1089 = !lean_is_exclusive(x_1071);
if (x_1089 == 0)
{
return x_1071;
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1090 = lean_ctor_get(x_1071, 0);
x_1091 = lean_ctor_get(x_1071, 1);
lean_inc(x_1091);
lean_inc(x_1090);
lean_dec(x_1071);
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
return x_1092;
}
}
}
else
{
lean_object* x_1093; 
x_1093 = lean_box(0);
x_994 = x_1093;
goto block_1066;
}
}
else
{
lean_object* x_1094; 
lean_dec(x_992);
x_1094 = lean_box(0);
x_994 = x_1094;
goto block_1066;
}
block_1066:
{
lean_object* x_995; 
lean_dec(x_994);
x_995 = l_Lean_ConstantInfo_value_x3f(x_987);
lean_dec(x_987);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_989);
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_978);
lean_dec(x_971);
lean_dec(x_1);
x_996 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_996, 0, x_982);
x_997 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_998 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_996);
x_999 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1000 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
x_1001 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1002 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1002, 0, x_1001);
x_1003 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1003, 0, x_1002);
x_1004 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1004, 0, x_1000);
lean_ctor_set(x_1004, 1, x_1003);
x_1005 = l_Lean_Core_getConstInfo___closed__5;
x_1006 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1006, 0, x_1004);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = l_Lean_Meta_throwError___rarg(x_1006, x_3, x_4, x_5, x_6, x_993);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1007;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_982);
lean_dec(x_9);
x_1008 = lean_ctor_get(x_995, 0);
lean_inc(x_1008);
lean_dec(x_995);
x_1009 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1008);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1010 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1009, x_3, x_4, x_5, x_6, x_993);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
x_1030 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1031 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed), 9, 2);
lean_closure_set(x_1031, 0, x_1);
lean_closure_set(x_1031, 1, x_1030);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1032 = l_Lean_Meta_forallTelescope___rarg(x_989, x_1031, x_3, x_4, x_5, x_6, x_1012);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; uint8_t x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1035 = lean_box(0);
lean_inc(x_985);
x_1036 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1036, 0, x_985);
lean_ctor_set(x_1036, 1, x_1035);
lean_ctor_set(x_1036, 2, x_1033);
x_1037 = lean_box(0);
x_1038 = 0;
x_1039 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1039, 0, x_1036);
lean_ctor_set(x_1039, 1, x_1011);
lean_ctor_set(x_1039, 2, x_1037);
lean_ctor_set_uint8(x_1039, sizeof(void*)*3, x_1038);
x_1040 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1040, 0, x_1039);
x_1041 = l_Lean_Core_getEnv___rarg(x_6, x_1034);
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
x_1044 = l_Lean_Options_empty;
x_1045 = l_Lean_Environment_addAndCompile(x_1042, x_1044, x_1040);
lean_dec(x_1040);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; 
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_978);
lean_dec(x_971);
lean_dec(x_1);
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
lean_dec(x_1045);
x_1047 = l_Lean_KernelException_toMessageData(x_1046, x_1044);
x_1048 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1047);
x_1049 = l_Lean_Format_pretty(x_1048, x_1044);
x_1050 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1050, 0, x_1049);
x_1051 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1051, 0, x_1050);
x_1052 = l_Lean_Meta_throwError___rarg(x_1051, x_3, x_4, x_5, x_6, x_1043);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1053 = !lean_is_exclusive(x_1052);
if (x_1053 == 0)
{
return x_1052;
}
else
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1054 = lean_ctor_get(x_1052, 0);
x_1055 = lean_ctor_get(x_1052, 1);
lean_inc(x_1055);
lean_inc(x_1054);
lean_dec(x_1052);
x_1056 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1056, 0, x_1054);
lean_ctor_set(x_1056, 1, x_1055);
return x_1056;
}
}
else
{
lean_object* x_1057; 
x_1057 = lean_ctor_get(x_1045, 0);
lean_inc(x_1057);
lean_dec(x_1045);
x_1013 = x_1057;
x_1014 = x_1043;
goto block_1029;
}
}
else
{
uint8_t x_1058; 
lean_dec(x_1011);
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_978);
lean_dec(x_971);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1058 = !lean_is_exclusive(x_1032);
if (x_1058 == 0)
{
return x_1032;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_1032, 0);
x_1060 = lean_ctor_get(x_1032, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_1032);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_1060);
return x_1061;
}
}
block_1029:
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_inc(x_985);
x_1015 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_983, x_1013, x_971, x_985);
x_1016 = l_Lean_Meta_setEnv(x_1015, x_3, x_4, x_5, x_6, x_1014);
x_1017 = lean_ctor_get(x_1016, 1);
lean_inc(x_1017);
lean_dec(x_1016);
x_1018 = lean_box(0);
x_1019 = l_Lean_mkConst(x_985, x_1018);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1019);
x_1020 = l_Lean_Meta_inferType(x_1019, x_3, x_4, x_5, x_6, x_1017);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1021 = lean_ctor_get(x_1020, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1020, 1);
lean_inc(x_1022);
lean_dec(x_1020);
x_1023 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed), 11, 4);
lean_closure_set(x_1023, 0, x_1);
lean_closure_set(x_1023, 1, x_990);
lean_closure_set(x_1023, 2, x_978);
lean_closure_set(x_1023, 3, x_1019);
x_1024 = l_Lean_Meta_forallTelescope___rarg(x_1021, x_1023, x_3, x_4, x_5, x_6, x_1022);
return x_1024;
}
else
{
uint8_t x_1025; 
lean_dec(x_1019);
lean_dec(x_978);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1025 = !lean_is_exclusive(x_1020);
if (x_1025 == 0)
{
return x_1020;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1026 = lean_ctor_get(x_1020, 0);
x_1027 = lean_ctor_get(x_1020, 1);
lean_inc(x_1027);
lean_inc(x_1026);
lean_dec(x_1020);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
return x_1028;
}
}
}
}
else
{
uint8_t x_1062; 
lean_dec(x_989);
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_978);
lean_dec(x_971);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1062 = !lean_is_exclusive(x_1010);
if (x_1062 == 0)
{
return x_1010;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1010, 0);
x_1064 = lean_ctor_get(x_1010, 1);
lean_inc(x_1064);
lean_inc(x_1063);
lean_dec(x_1010);
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1063);
lean_ctor_set(x_1065, 1, x_1064);
return x_1065;
}
}
}
}
}
else
{
uint8_t x_1095; 
lean_dec(x_989);
lean_dec(x_987);
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_982);
lean_dec(x_978);
lean_dec(x_971);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1095 = !lean_is_exclusive(x_991);
if (x_1095 == 0)
{
return x_991;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_991, 0);
x_1097 = lean_ctor_get(x_991, 1);
lean_inc(x_1097);
lean_inc(x_1096);
lean_dec(x_991);
x_1098 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
return x_1098;
}
}
}
else
{
uint8_t x_1099; 
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_982);
lean_dec(x_978);
lean_dec(x_971);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1099 = !lean_is_exclusive(x_986);
if (x_1099 == 0)
{
return x_986;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1100 = lean_ctor_get(x_986, 0);
x_1101 = lean_ctor_get(x_986, 1);
lean_inc(x_1101);
lean_inc(x_1100);
lean_dec(x_986);
x_1102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1102, 0, x_1100);
lean_ctor_set(x_1102, 1, x_1101);
return x_1102;
}
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_983);
lean_dec(x_982);
lean_dec(x_971);
lean_dec(x_9);
x_1103 = lean_ctor_get(x_984, 0);
lean_inc(x_1103);
lean_dec(x_984);
x_1104 = lean_box(0);
x_1105 = l_Lean_mkConst(x_1103, x_1104);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1105);
x_1106 = l_Lean_Meta_inferType(x_1105, x_3, x_4, x_5, x_6, x_981);
if (lean_obj_tag(x_1106) == 0)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1107 = lean_ctor_get(x_1106, 0);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_1106, 1);
lean_inc(x_1108);
lean_dec(x_1106);
x_1109 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed), 10, 3);
lean_closure_set(x_1109, 0, x_1);
lean_closure_set(x_1109, 1, x_978);
lean_closure_set(x_1109, 2, x_1105);
x_1110 = l_Lean_Meta_forallTelescope___rarg(x_1107, x_1109, x_3, x_4, x_5, x_6, x_1108);
return x_1110;
}
else
{
uint8_t x_1111; 
lean_dec(x_1105);
lean_dec(x_978);
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
}
else
{
lean_object* x_1115; 
lean_dec(x_960);
lean_dec(x_1);
x_1115 = lean_box(0);
x_961 = x_1115;
goto block_970;
}
block_970:
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
lean_dec(x_961);
x_962 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_963 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_963, 0, x_962);
x_964 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_964, 0, x_963);
x_965 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_966 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_966, 0, x_965);
lean_ctor_set(x_966, 1, x_964);
x_967 = l_Lean_Core_getConstInfo___closed__5;
x_968 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_968, 0, x_966);
lean_ctor_set(x_968, 1, x_967);
x_969 = l_Lean_Meta_throwError___rarg(x_968, x_3, x_4, x_5, x_6, x_959);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_969;
}
}
case 9:
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_8, 1);
lean_inc(x_1116);
lean_dec(x_8);
x_1117 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1117) == 4)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1128 = lean_ctor_get(x_1117, 0);
lean_inc(x_1128);
lean_dec(x_1117);
x_1129 = lean_unsigned_to_nat(0u);
x_1130 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1129);
x_1131 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1130);
x_1132 = lean_mk_array(x_1130, x_1131);
x_1133 = lean_unsigned_to_nat(1u);
x_1134 = lean_nat_sub(x_1130, x_1133);
lean_dec(x_1130);
lean_inc(x_9);
x_1135 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1132, x_1134);
x_1136 = l_Lean_Core_getEnv___rarg(x_6, x_1116);
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1136, 1);
lean_inc(x_1138);
lean_dec(x_1136);
x_1139 = lean_ctor_get(x_1, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1, 2);
lean_inc(x_1140);
x_1141 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1140, x_1137, x_1128);
lean_dec(x_1137);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; 
lean_inc(x_1139);
x_1142 = l_Lean_Name_append___main(x_1128, x_1139);
lean_inc(x_1128);
x_1143 = l_Lean_Meta_getConstInfo(x_1128, x_3, x_4, x_5, x_6, x_1138);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1143, 1);
lean_inc(x_1145);
lean_dec(x_1143);
x_1146 = l_Lean_ConstantInfo_type(x_1144);
x_1147 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1146);
x_1148 = l_Lean_Meta_forallTelescope___rarg(x_1146, x_1147, x_3, x_4, x_5, x_6, x_1145);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1224; uint8_t x_1225; 
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
lean_dec(x_1148);
x_1224 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1225 = l_Lean_Expr_isConstOf(x_1149, x_1224);
if (x_1225 == 0)
{
lean_object* x_1226; uint8_t x_1227; 
x_1226 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1227 = l_Lean_Expr_isConstOf(x_1149, x_1226);
lean_dec(x_1149);
if (x_1227 == 0)
{
lean_object* x_1228; 
lean_dec(x_1146);
lean_dec(x_1144);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1135);
lean_dec(x_1128);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1228 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1150);
if (lean_obj_tag(x_1228) == 0)
{
lean_object* x_1229; 
x_1229 = lean_ctor_get(x_1228, 0);
lean_inc(x_1229);
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
lean_dec(x_1);
x_1230 = lean_ctor_get(x_1228, 1);
lean_inc(x_1230);
lean_dec(x_1228);
x_1231 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1231, 0, x_1139);
x_1232 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1233 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1233, 1, x_1231);
x_1234 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1235 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1235, 0, x_1233);
lean_ctor_set(x_1235, 1, x_1234);
x_1236 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1237 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1237, 0, x_1236);
x_1238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1238, 0, x_1237);
x_1239 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1239, 0, x_1235);
lean_ctor_set(x_1239, 1, x_1238);
x_1240 = l_Lean_Core_getConstInfo___closed__5;
x_1241 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1241, 0, x_1239);
lean_ctor_set(x_1241, 1, x_1240);
x_1242 = l_Lean_Meta_throwError___rarg(x_1241, x_3, x_4, x_5, x_6, x_1230);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1242;
}
else
{
lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_1139);
lean_dec(x_9);
x_1243 = lean_ctor_get(x_1228, 1);
lean_inc(x_1243);
lean_dec(x_1228);
x_1244 = lean_ctor_get(x_1229, 0);
lean_inc(x_1244);
lean_dec(x_1229);
x_2 = x_1244;
x_7 = x_1243;
goto _start;
}
}
else
{
uint8_t x_1246; 
lean_dec(x_1139);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1246 = !lean_is_exclusive(x_1228);
if (x_1246 == 0)
{
return x_1228;
}
else
{
lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; 
x_1247 = lean_ctor_get(x_1228, 0);
x_1248 = lean_ctor_get(x_1228, 1);
lean_inc(x_1248);
lean_inc(x_1247);
lean_dec(x_1228);
x_1249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1249, 0, x_1247);
lean_ctor_set(x_1249, 1, x_1248);
return x_1249;
}
}
}
else
{
lean_object* x_1250; 
x_1250 = lean_box(0);
x_1151 = x_1250;
goto block_1223;
}
}
else
{
lean_object* x_1251; 
lean_dec(x_1149);
x_1251 = lean_box(0);
x_1151 = x_1251;
goto block_1223;
}
block_1223:
{
lean_object* x_1152; 
lean_dec(x_1151);
x_1152 = l_Lean_ConstantInfo_value_x3f(x_1144);
lean_dec(x_1144);
if (lean_obj_tag(x_1152) == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1146);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1135);
lean_dec(x_1128);
lean_dec(x_1);
x_1153 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1153, 0, x_1139);
x_1154 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1155 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_1153);
x_1156 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1157 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set(x_1157, 1, x_1156);
x_1158 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1159, 0, x_1158);
x_1160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1160, 0, x_1159);
x_1161 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1161, 0, x_1157);
lean_ctor_set(x_1161, 1, x_1160);
x_1162 = l_Lean_Core_getConstInfo___closed__5;
x_1163 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
x_1164 = l_Lean_Meta_throwError___rarg(x_1163, x_3, x_4, x_5, x_6, x_1150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1164;
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
lean_dec(x_1139);
lean_dec(x_9);
x_1165 = lean_ctor_get(x_1152, 0);
lean_inc(x_1165);
lean_dec(x_1152);
x_1166 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1165);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1167 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1166, x_3, x_4, x_5, x_6, x_1150);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
x_1187 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1188 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed), 9, 2);
lean_closure_set(x_1188, 0, x_1);
lean_closure_set(x_1188, 1, x_1187);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1189 = l_Lean_Meta_forallTelescope___rarg(x_1146, x_1188, x_3, x_4, x_5, x_6, x_1169);
if (lean_obj_tag(x_1189) == 0)
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; uint8_t x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1189, 1);
lean_inc(x_1191);
lean_dec(x_1189);
x_1192 = lean_box(0);
lean_inc(x_1142);
x_1193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1193, 0, x_1142);
lean_ctor_set(x_1193, 1, x_1192);
lean_ctor_set(x_1193, 2, x_1190);
x_1194 = lean_box(0);
x_1195 = 0;
x_1196 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1196, 0, x_1193);
lean_ctor_set(x_1196, 1, x_1168);
lean_ctor_set(x_1196, 2, x_1194);
lean_ctor_set_uint8(x_1196, sizeof(void*)*3, x_1195);
x_1197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1197, 0, x_1196);
x_1198 = l_Lean_Core_getEnv___rarg(x_6, x_1191);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_1201 = l_Lean_Options_empty;
x_1202 = l_Lean_Environment_addAndCompile(x_1199, x_1201, x_1197);
lean_dec(x_1197);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; uint8_t x_1210; 
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1135);
lean_dec(x_1128);
lean_dec(x_1);
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
lean_dec(x_1202);
x_1204 = l_Lean_KernelException_toMessageData(x_1203, x_1201);
x_1205 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1204);
x_1206 = l_Lean_Format_pretty(x_1205, x_1201);
x_1207 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1207, 0, x_1206);
x_1208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1208, 0, x_1207);
x_1209 = l_Lean_Meta_throwError___rarg(x_1208, x_3, x_4, x_5, x_6, x_1200);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1210 = !lean_is_exclusive(x_1209);
if (x_1210 == 0)
{
return x_1209;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1211 = lean_ctor_get(x_1209, 0);
x_1212 = lean_ctor_get(x_1209, 1);
lean_inc(x_1212);
lean_inc(x_1211);
lean_dec(x_1209);
x_1213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1213, 0, x_1211);
lean_ctor_set(x_1213, 1, x_1212);
return x_1213;
}
}
else
{
lean_object* x_1214; 
x_1214 = lean_ctor_get(x_1202, 0);
lean_inc(x_1214);
lean_dec(x_1202);
x_1170 = x_1214;
x_1171 = x_1200;
goto block_1186;
}
}
else
{
uint8_t x_1215; 
lean_dec(x_1168);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1135);
lean_dec(x_1128);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1215 = !lean_is_exclusive(x_1189);
if (x_1215 == 0)
{
return x_1189;
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
x_1216 = lean_ctor_get(x_1189, 0);
x_1217 = lean_ctor_get(x_1189, 1);
lean_inc(x_1217);
lean_inc(x_1216);
lean_dec(x_1189);
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1216);
lean_ctor_set(x_1218, 1, x_1217);
return x_1218;
}
}
block_1186:
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
lean_inc(x_1142);
x_1172 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1140, x_1170, x_1128, x_1142);
x_1173 = l_Lean_Meta_setEnv(x_1172, x_3, x_4, x_5, x_6, x_1171);
x_1174 = lean_ctor_get(x_1173, 1);
lean_inc(x_1174);
lean_dec(x_1173);
x_1175 = lean_box(0);
x_1176 = l_Lean_mkConst(x_1142, x_1175);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1176);
x_1177 = l_Lean_Meta_inferType(x_1176, x_3, x_4, x_5, x_6, x_1174);
if (lean_obj_tag(x_1177) == 0)
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
x_1178 = lean_ctor_get(x_1177, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1177, 1);
lean_inc(x_1179);
lean_dec(x_1177);
x_1180 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed), 11, 4);
lean_closure_set(x_1180, 0, x_1);
lean_closure_set(x_1180, 1, x_1147);
lean_closure_set(x_1180, 2, x_1135);
lean_closure_set(x_1180, 3, x_1176);
x_1181 = l_Lean_Meta_forallTelescope___rarg(x_1178, x_1180, x_3, x_4, x_5, x_6, x_1179);
return x_1181;
}
else
{
uint8_t x_1182; 
lean_dec(x_1176);
lean_dec(x_1135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1182 = !lean_is_exclusive(x_1177);
if (x_1182 == 0)
{
return x_1177;
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
x_1183 = lean_ctor_get(x_1177, 0);
x_1184 = lean_ctor_get(x_1177, 1);
lean_inc(x_1184);
lean_inc(x_1183);
lean_dec(x_1177);
x_1185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1185, 0, x_1183);
lean_ctor_set(x_1185, 1, x_1184);
return x_1185;
}
}
}
}
else
{
uint8_t x_1219; 
lean_dec(x_1146);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1135);
lean_dec(x_1128);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1219 = !lean_is_exclusive(x_1167);
if (x_1219 == 0)
{
return x_1167;
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
x_1220 = lean_ctor_get(x_1167, 0);
x_1221 = lean_ctor_get(x_1167, 1);
lean_inc(x_1221);
lean_inc(x_1220);
lean_dec(x_1167);
x_1222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1222, 0, x_1220);
lean_ctor_set(x_1222, 1, x_1221);
return x_1222;
}
}
}
}
}
else
{
uint8_t x_1252; 
lean_dec(x_1146);
lean_dec(x_1144);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1139);
lean_dec(x_1135);
lean_dec(x_1128);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1252 = !lean_is_exclusive(x_1148);
if (x_1252 == 0)
{
return x_1148;
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1253 = lean_ctor_get(x_1148, 0);
x_1254 = lean_ctor_get(x_1148, 1);
lean_inc(x_1254);
lean_inc(x_1253);
lean_dec(x_1148);
x_1255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1255, 0, x_1253);
lean_ctor_set(x_1255, 1, x_1254);
return x_1255;
}
}
}
else
{
uint8_t x_1256; 
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1139);
lean_dec(x_1135);
lean_dec(x_1128);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1256 = !lean_is_exclusive(x_1143);
if (x_1256 == 0)
{
return x_1143;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1257 = lean_ctor_get(x_1143, 0);
x_1258 = lean_ctor_get(x_1143, 1);
lean_inc(x_1258);
lean_inc(x_1257);
lean_dec(x_1143);
x_1259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1259, 0, x_1257);
lean_ctor_set(x_1259, 1, x_1258);
return x_1259;
}
}
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
lean_dec(x_1140);
lean_dec(x_1139);
lean_dec(x_1128);
lean_dec(x_9);
x_1260 = lean_ctor_get(x_1141, 0);
lean_inc(x_1260);
lean_dec(x_1141);
x_1261 = lean_box(0);
x_1262 = l_Lean_mkConst(x_1260, x_1261);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1262);
x_1263 = l_Lean_Meta_inferType(x_1262, x_3, x_4, x_5, x_6, x_1138);
if (lean_obj_tag(x_1263) == 0)
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1263, 1);
lean_inc(x_1265);
lean_dec(x_1263);
x_1266 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed), 10, 3);
lean_closure_set(x_1266, 0, x_1);
lean_closure_set(x_1266, 1, x_1135);
lean_closure_set(x_1266, 2, x_1262);
x_1267 = l_Lean_Meta_forallTelescope___rarg(x_1264, x_1266, x_3, x_4, x_5, x_6, x_1265);
return x_1267;
}
else
{
uint8_t x_1268; 
lean_dec(x_1262);
lean_dec(x_1135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1268 = !lean_is_exclusive(x_1263);
if (x_1268 == 0)
{
return x_1263;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
x_1269 = lean_ctor_get(x_1263, 0);
x_1270 = lean_ctor_get(x_1263, 1);
lean_inc(x_1270);
lean_inc(x_1269);
lean_dec(x_1263);
x_1271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1271, 0, x_1269);
lean_ctor_set(x_1271, 1, x_1270);
return x_1271;
}
}
}
}
else
{
lean_object* x_1272; 
lean_dec(x_1117);
lean_dec(x_1);
x_1272 = lean_box(0);
x_1118 = x_1272;
goto block_1127;
}
block_1127:
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_1118);
x_1119 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1120, 0, x_1119);
x_1121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1121, 0, x_1120);
x_1122 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1123, 0, x_1122);
lean_ctor_set(x_1123, 1, x_1121);
x_1124 = l_Lean_Core_getConstInfo___closed__5;
x_1125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
x_1126 = l_Lean_Meta_throwError___rarg(x_1125, x_3, x_4, x_5, x_6, x_1116);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1126;
}
}
case 10:
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
x_1273 = lean_ctor_get(x_8, 1);
lean_inc(x_1273);
lean_dec(x_8);
x_1274 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1274) == 4)
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
x_1285 = lean_ctor_get(x_1274, 0);
lean_inc(x_1285);
lean_dec(x_1274);
x_1286 = lean_unsigned_to_nat(0u);
x_1287 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1286);
x_1288 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1287);
x_1289 = lean_mk_array(x_1287, x_1288);
x_1290 = lean_unsigned_to_nat(1u);
x_1291 = lean_nat_sub(x_1287, x_1290);
lean_dec(x_1287);
lean_inc(x_9);
x_1292 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1289, x_1291);
x_1293 = l_Lean_Core_getEnv___rarg(x_6, x_1273);
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1293, 1);
lean_inc(x_1295);
lean_dec(x_1293);
x_1296 = lean_ctor_get(x_1, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1, 2);
lean_inc(x_1297);
x_1298 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1297, x_1294, x_1285);
lean_dec(x_1294);
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1299; lean_object* x_1300; 
lean_inc(x_1296);
x_1299 = l_Lean_Name_append___main(x_1285, x_1296);
lean_inc(x_1285);
x_1300 = l_Lean_Meta_getConstInfo(x_1285, x_3, x_4, x_5, x_6, x_1295);
if (lean_obj_tag(x_1300) == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
lean_dec(x_1300);
x_1303 = l_Lean_ConstantInfo_type(x_1301);
x_1304 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1303);
x_1305 = l_Lean_Meta_forallTelescope___rarg(x_1303, x_1304, x_3, x_4, x_5, x_6, x_1302);
if (lean_obj_tag(x_1305) == 0)
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1381; uint8_t x_1382; 
x_1306 = lean_ctor_get(x_1305, 0);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1305, 1);
lean_inc(x_1307);
lean_dec(x_1305);
x_1381 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1382 = l_Lean_Expr_isConstOf(x_1306, x_1381);
if (x_1382 == 0)
{
lean_object* x_1383; uint8_t x_1384; 
x_1383 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1384 = l_Lean_Expr_isConstOf(x_1306, x_1383);
lean_dec(x_1306);
if (x_1384 == 0)
{
lean_object* x_1385; 
lean_dec(x_1303);
lean_dec(x_1301);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1292);
lean_dec(x_1285);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1385 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1307);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; 
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
if (lean_obj_tag(x_1386) == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
lean_dec(x_1);
x_1387 = lean_ctor_get(x_1385, 1);
lean_inc(x_1387);
lean_dec(x_1385);
x_1388 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1388, 0, x_1296);
x_1389 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1390 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1390, 0, x_1389);
lean_ctor_set(x_1390, 1, x_1388);
x_1391 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1392, 0, x_1390);
lean_ctor_set(x_1392, 1, x_1391);
x_1393 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1394 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1394, 0, x_1393);
x_1395 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1395, 0, x_1394);
x_1396 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1396, 0, x_1392);
lean_ctor_set(x_1396, 1, x_1395);
x_1397 = l_Lean_Core_getConstInfo___closed__5;
x_1398 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1398, 0, x_1396);
lean_ctor_set(x_1398, 1, x_1397);
x_1399 = l_Lean_Meta_throwError___rarg(x_1398, x_3, x_4, x_5, x_6, x_1387);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1399;
}
else
{
lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1296);
lean_dec(x_9);
x_1400 = lean_ctor_get(x_1385, 1);
lean_inc(x_1400);
lean_dec(x_1385);
x_1401 = lean_ctor_get(x_1386, 0);
lean_inc(x_1401);
lean_dec(x_1386);
x_2 = x_1401;
x_7 = x_1400;
goto _start;
}
}
else
{
uint8_t x_1403; 
lean_dec(x_1296);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1403 = !lean_is_exclusive(x_1385);
if (x_1403 == 0)
{
return x_1385;
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1404 = lean_ctor_get(x_1385, 0);
x_1405 = lean_ctor_get(x_1385, 1);
lean_inc(x_1405);
lean_inc(x_1404);
lean_dec(x_1385);
x_1406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1406, 0, x_1404);
lean_ctor_set(x_1406, 1, x_1405);
return x_1406;
}
}
}
else
{
lean_object* x_1407; 
x_1407 = lean_box(0);
x_1308 = x_1407;
goto block_1380;
}
}
else
{
lean_object* x_1408; 
lean_dec(x_1306);
x_1408 = lean_box(0);
x_1308 = x_1408;
goto block_1380;
}
block_1380:
{
lean_object* x_1309; 
lean_dec(x_1308);
x_1309 = l_Lean_ConstantInfo_value_x3f(x_1301);
lean_dec(x_1301);
if (lean_obj_tag(x_1309) == 0)
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
lean_dec(x_1303);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1292);
lean_dec(x_1285);
lean_dec(x_1);
x_1310 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1310, 0, x_1296);
x_1311 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1312 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1312, 0, x_1311);
lean_ctor_set(x_1312, 1, x_1310);
x_1313 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1314, 0, x_1312);
lean_ctor_set(x_1314, 1, x_1313);
x_1315 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1316 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1316, 0, x_1315);
x_1317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1317, 0, x_1316);
x_1318 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1318, 0, x_1314);
lean_ctor_set(x_1318, 1, x_1317);
x_1319 = l_Lean_Core_getConstInfo___closed__5;
x_1320 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1320, 0, x_1318);
lean_ctor_set(x_1320, 1, x_1319);
x_1321 = l_Lean_Meta_throwError___rarg(x_1320, x_3, x_4, x_5, x_6, x_1307);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1321;
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
lean_dec(x_1296);
lean_dec(x_9);
x_1322 = lean_ctor_get(x_1309, 0);
lean_inc(x_1322);
lean_dec(x_1309);
x_1323 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1322);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1324 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1323, x_3, x_4, x_5, x_6, x_1307);
if (lean_obj_tag(x_1324) == 0)
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
x_1325 = lean_ctor_get(x_1324, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1324, 1);
lean_inc(x_1326);
lean_dec(x_1324);
x_1344 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1345 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed), 9, 2);
lean_closure_set(x_1345, 0, x_1);
lean_closure_set(x_1345, 1, x_1344);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1346 = l_Lean_Meta_forallTelescope___rarg(x_1303, x_1345, x_3, x_4, x_5, x_6, x_1326);
if (lean_obj_tag(x_1346) == 0)
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
x_1347 = lean_ctor_get(x_1346, 0);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1346, 1);
lean_inc(x_1348);
lean_dec(x_1346);
x_1349 = lean_box(0);
lean_inc(x_1299);
x_1350 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1350, 0, x_1299);
lean_ctor_set(x_1350, 1, x_1349);
lean_ctor_set(x_1350, 2, x_1347);
x_1351 = lean_box(0);
x_1352 = 0;
x_1353 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1353, 0, x_1350);
lean_ctor_set(x_1353, 1, x_1325);
lean_ctor_set(x_1353, 2, x_1351);
lean_ctor_set_uint8(x_1353, sizeof(void*)*3, x_1352);
x_1354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1354, 0, x_1353);
x_1355 = l_Lean_Core_getEnv___rarg(x_6, x_1348);
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
x_1357 = lean_ctor_get(x_1355, 1);
lean_inc(x_1357);
lean_dec(x_1355);
x_1358 = l_Lean_Options_empty;
x_1359 = l_Lean_Environment_addAndCompile(x_1356, x_1358, x_1354);
lean_dec(x_1354);
if (lean_obj_tag(x_1359) == 0)
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; 
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1292);
lean_dec(x_1285);
lean_dec(x_1);
x_1360 = lean_ctor_get(x_1359, 0);
lean_inc(x_1360);
lean_dec(x_1359);
x_1361 = l_Lean_KernelException_toMessageData(x_1360, x_1358);
x_1362 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1361);
x_1363 = l_Lean_Format_pretty(x_1362, x_1358);
x_1364 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1364, 0, x_1363);
x_1365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1365, 0, x_1364);
x_1366 = l_Lean_Meta_throwError___rarg(x_1365, x_3, x_4, x_5, x_6, x_1357);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1367 = !lean_is_exclusive(x_1366);
if (x_1367 == 0)
{
return x_1366;
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
x_1368 = lean_ctor_get(x_1366, 0);
x_1369 = lean_ctor_get(x_1366, 1);
lean_inc(x_1369);
lean_inc(x_1368);
lean_dec(x_1366);
x_1370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1370, 0, x_1368);
lean_ctor_set(x_1370, 1, x_1369);
return x_1370;
}
}
else
{
lean_object* x_1371; 
x_1371 = lean_ctor_get(x_1359, 0);
lean_inc(x_1371);
lean_dec(x_1359);
x_1327 = x_1371;
x_1328 = x_1357;
goto block_1343;
}
}
else
{
uint8_t x_1372; 
lean_dec(x_1325);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1292);
lean_dec(x_1285);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1372 = !lean_is_exclusive(x_1346);
if (x_1372 == 0)
{
return x_1346;
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1373 = lean_ctor_get(x_1346, 0);
x_1374 = lean_ctor_get(x_1346, 1);
lean_inc(x_1374);
lean_inc(x_1373);
lean_dec(x_1346);
x_1375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1375, 0, x_1373);
lean_ctor_set(x_1375, 1, x_1374);
return x_1375;
}
}
block_1343:
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
lean_inc(x_1299);
x_1329 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1297, x_1327, x_1285, x_1299);
x_1330 = l_Lean_Meta_setEnv(x_1329, x_3, x_4, x_5, x_6, x_1328);
x_1331 = lean_ctor_get(x_1330, 1);
lean_inc(x_1331);
lean_dec(x_1330);
x_1332 = lean_box(0);
x_1333 = l_Lean_mkConst(x_1299, x_1332);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1333);
x_1334 = l_Lean_Meta_inferType(x_1333, x_3, x_4, x_5, x_6, x_1331);
if (lean_obj_tag(x_1334) == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
lean_dec(x_1334);
x_1337 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed), 11, 4);
lean_closure_set(x_1337, 0, x_1);
lean_closure_set(x_1337, 1, x_1304);
lean_closure_set(x_1337, 2, x_1292);
lean_closure_set(x_1337, 3, x_1333);
x_1338 = l_Lean_Meta_forallTelescope___rarg(x_1335, x_1337, x_3, x_4, x_5, x_6, x_1336);
return x_1338;
}
else
{
uint8_t x_1339; 
lean_dec(x_1333);
lean_dec(x_1292);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1339 = !lean_is_exclusive(x_1334);
if (x_1339 == 0)
{
return x_1334;
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
x_1340 = lean_ctor_get(x_1334, 0);
x_1341 = lean_ctor_get(x_1334, 1);
lean_inc(x_1341);
lean_inc(x_1340);
lean_dec(x_1334);
x_1342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1342, 0, x_1340);
lean_ctor_set(x_1342, 1, x_1341);
return x_1342;
}
}
}
}
else
{
uint8_t x_1376; 
lean_dec(x_1303);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1292);
lean_dec(x_1285);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1376 = !lean_is_exclusive(x_1324);
if (x_1376 == 0)
{
return x_1324;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1377 = lean_ctor_get(x_1324, 0);
x_1378 = lean_ctor_get(x_1324, 1);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_1324);
x_1379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
return x_1379;
}
}
}
}
}
else
{
uint8_t x_1409; 
lean_dec(x_1303);
lean_dec(x_1301);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1292);
lean_dec(x_1285);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1409 = !lean_is_exclusive(x_1305);
if (x_1409 == 0)
{
return x_1305;
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
x_1410 = lean_ctor_get(x_1305, 0);
x_1411 = lean_ctor_get(x_1305, 1);
lean_inc(x_1411);
lean_inc(x_1410);
lean_dec(x_1305);
x_1412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1412, 0, x_1410);
lean_ctor_set(x_1412, 1, x_1411);
return x_1412;
}
}
}
else
{
uint8_t x_1413; 
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1292);
lean_dec(x_1285);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1413 = !lean_is_exclusive(x_1300);
if (x_1413 == 0)
{
return x_1300;
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1414 = lean_ctor_get(x_1300, 0);
x_1415 = lean_ctor_get(x_1300, 1);
lean_inc(x_1415);
lean_inc(x_1414);
lean_dec(x_1300);
x_1416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1416, 0, x_1414);
lean_ctor_set(x_1416, 1, x_1415);
return x_1416;
}
}
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1285);
lean_dec(x_9);
x_1417 = lean_ctor_get(x_1298, 0);
lean_inc(x_1417);
lean_dec(x_1298);
x_1418 = lean_box(0);
x_1419 = l_Lean_mkConst(x_1417, x_1418);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1419);
x_1420 = l_Lean_Meta_inferType(x_1419, x_3, x_4, x_5, x_6, x_1295);
if (lean_obj_tag(x_1420) == 0)
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1421 = lean_ctor_get(x_1420, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1420, 1);
lean_inc(x_1422);
lean_dec(x_1420);
x_1423 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed), 10, 3);
lean_closure_set(x_1423, 0, x_1);
lean_closure_set(x_1423, 1, x_1292);
lean_closure_set(x_1423, 2, x_1419);
x_1424 = l_Lean_Meta_forallTelescope___rarg(x_1421, x_1423, x_3, x_4, x_5, x_6, x_1422);
return x_1424;
}
else
{
uint8_t x_1425; 
lean_dec(x_1419);
lean_dec(x_1292);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1425 = !lean_is_exclusive(x_1420);
if (x_1425 == 0)
{
return x_1420;
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
x_1426 = lean_ctor_get(x_1420, 0);
x_1427 = lean_ctor_get(x_1420, 1);
lean_inc(x_1427);
lean_inc(x_1426);
lean_dec(x_1420);
x_1428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1428, 0, x_1426);
lean_ctor_set(x_1428, 1, x_1427);
return x_1428;
}
}
}
}
else
{
lean_object* x_1429; 
lean_dec(x_1274);
lean_dec(x_1);
x_1429 = lean_box(0);
x_1275 = x_1429;
goto block_1284;
}
block_1284:
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1275);
x_1276 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1277 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1277, 0, x_1276);
x_1278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1278, 0, x_1277);
x_1279 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1280 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1280, 0, x_1279);
lean_ctor_set(x_1280, 1, x_1278);
x_1281 = l_Lean_Core_getConstInfo___closed__5;
x_1282 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1282, 0, x_1280);
lean_ctor_set(x_1282, 1, x_1281);
x_1283 = l_Lean_Meta_throwError___rarg(x_1282, x_3, x_4, x_5, x_6, x_1273);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1283;
}
}
case 11:
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
x_1430 = lean_ctor_get(x_8, 1);
lean_inc(x_1430);
lean_dec(x_8);
x_1431 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1431) == 4)
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
x_1442 = lean_ctor_get(x_1431, 0);
lean_inc(x_1442);
lean_dec(x_1431);
x_1443 = lean_unsigned_to_nat(0u);
x_1444 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1443);
x_1445 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1444);
x_1446 = lean_mk_array(x_1444, x_1445);
x_1447 = lean_unsigned_to_nat(1u);
x_1448 = lean_nat_sub(x_1444, x_1447);
lean_dec(x_1444);
lean_inc(x_9);
x_1449 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1446, x_1448);
x_1450 = l_Lean_Core_getEnv___rarg(x_6, x_1430);
x_1451 = lean_ctor_get(x_1450, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1450, 1);
lean_inc(x_1452);
lean_dec(x_1450);
x_1453 = lean_ctor_get(x_1, 0);
lean_inc(x_1453);
x_1454 = lean_ctor_get(x_1, 2);
lean_inc(x_1454);
x_1455 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1454, x_1451, x_1442);
lean_dec(x_1451);
if (lean_obj_tag(x_1455) == 0)
{
lean_object* x_1456; lean_object* x_1457; 
lean_inc(x_1453);
x_1456 = l_Lean_Name_append___main(x_1442, x_1453);
lean_inc(x_1442);
x_1457 = l_Lean_Meta_getConstInfo(x_1442, x_3, x_4, x_5, x_6, x_1452);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
x_1460 = l_Lean_ConstantInfo_type(x_1458);
x_1461 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1460);
x_1462 = l_Lean_Meta_forallTelescope___rarg(x_1460, x_1461, x_3, x_4, x_5, x_6, x_1459);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1538; uint8_t x_1539; 
x_1463 = lean_ctor_get(x_1462, 0);
lean_inc(x_1463);
x_1464 = lean_ctor_get(x_1462, 1);
lean_inc(x_1464);
lean_dec(x_1462);
x_1538 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1539 = l_Lean_Expr_isConstOf(x_1463, x_1538);
if (x_1539 == 0)
{
lean_object* x_1540; uint8_t x_1541; 
x_1540 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1541 = l_Lean_Expr_isConstOf(x_1463, x_1540);
lean_dec(x_1463);
if (x_1541 == 0)
{
lean_object* x_1542; 
lean_dec(x_1460);
lean_dec(x_1458);
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1449);
lean_dec(x_1442);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1542 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1464);
if (lean_obj_tag(x_1542) == 0)
{
lean_object* x_1543; 
x_1543 = lean_ctor_get(x_1542, 0);
lean_inc(x_1543);
if (lean_obj_tag(x_1543) == 0)
{
lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; 
lean_dec(x_1);
x_1544 = lean_ctor_get(x_1542, 1);
lean_inc(x_1544);
lean_dec(x_1542);
x_1545 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1545, 0, x_1453);
x_1546 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1547 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1547, 0, x_1546);
lean_ctor_set(x_1547, 1, x_1545);
x_1548 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1549 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1549, 0, x_1547);
lean_ctor_set(x_1549, 1, x_1548);
x_1550 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1551 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1551, 0, x_1550);
x_1552 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1552, 0, x_1551);
x_1553 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1553, 0, x_1549);
lean_ctor_set(x_1553, 1, x_1552);
x_1554 = l_Lean_Core_getConstInfo___closed__5;
x_1555 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1555, 0, x_1553);
lean_ctor_set(x_1555, 1, x_1554);
x_1556 = l_Lean_Meta_throwError___rarg(x_1555, x_3, x_4, x_5, x_6, x_1544);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1556;
}
else
{
lean_object* x_1557; lean_object* x_1558; 
lean_dec(x_1453);
lean_dec(x_9);
x_1557 = lean_ctor_get(x_1542, 1);
lean_inc(x_1557);
lean_dec(x_1542);
x_1558 = lean_ctor_get(x_1543, 0);
lean_inc(x_1558);
lean_dec(x_1543);
x_2 = x_1558;
x_7 = x_1557;
goto _start;
}
}
else
{
uint8_t x_1560; 
lean_dec(x_1453);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1560 = !lean_is_exclusive(x_1542);
if (x_1560 == 0)
{
return x_1542;
}
else
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1561 = lean_ctor_get(x_1542, 0);
x_1562 = lean_ctor_get(x_1542, 1);
lean_inc(x_1562);
lean_inc(x_1561);
lean_dec(x_1542);
x_1563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1563, 0, x_1561);
lean_ctor_set(x_1563, 1, x_1562);
return x_1563;
}
}
}
else
{
lean_object* x_1564; 
x_1564 = lean_box(0);
x_1465 = x_1564;
goto block_1537;
}
}
else
{
lean_object* x_1565; 
lean_dec(x_1463);
x_1565 = lean_box(0);
x_1465 = x_1565;
goto block_1537;
}
block_1537:
{
lean_object* x_1466; 
lean_dec(x_1465);
x_1466 = l_Lean_ConstantInfo_value_x3f(x_1458);
lean_dec(x_1458);
if (lean_obj_tag(x_1466) == 0)
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
lean_dec(x_1460);
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1449);
lean_dec(x_1442);
lean_dec(x_1);
x_1467 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1467, 0, x_1453);
x_1468 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1469 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1469, 0, x_1468);
lean_ctor_set(x_1469, 1, x_1467);
x_1470 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1471 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1471, 0, x_1469);
lean_ctor_set(x_1471, 1, x_1470);
x_1472 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1473 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1473, 0, x_1472);
x_1474 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1474, 0, x_1473);
x_1475 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1475, 0, x_1471);
lean_ctor_set(x_1475, 1, x_1474);
x_1476 = l_Lean_Core_getConstInfo___closed__5;
x_1477 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1477, 0, x_1475);
lean_ctor_set(x_1477, 1, x_1476);
x_1478 = l_Lean_Meta_throwError___rarg(x_1477, x_3, x_4, x_5, x_6, x_1464);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1478;
}
else
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
lean_dec(x_1453);
lean_dec(x_9);
x_1479 = lean_ctor_get(x_1466, 0);
lean_inc(x_1479);
lean_dec(x_1466);
x_1480 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1479);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1481 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1480, x_3, x_4, x_5, x_6, x_1464);
if (lean_obj_tag(x_1481) == 0)
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
x_1482 = lean_ctor_get(x_1481, 0);
lean_inc(x_1482);
x_1483 = lean_ctor_get(x_1481, 1);
lean_inc(x_1483);
lean_dec(x_1481);
x_1501 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1502 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed), 9, 2);
lean_closure_set(x_1502, 0, x_1);
lean_closure_set(x_1502, 1, x_1501);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1503 = l_Lean_Meta_forallTelescope___rarg(x_1460, x_1502, x_3, x_4, x_5, x_6, x_1483);
if (lean_obj_tag(x_1503) == 0)
{
lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
x_1504 = lean_ctor_get(x_1503, 0);
lean_inc(x_1504);
x_1505 = lean_ctor_get(x_1503, 1);
lean_inc(x_1505);
lean_dec(x_1503);
x_1506 = lean_box(0);
lean_inc(x_1456);
x_1507 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1507, 0, x_1456);
lean_ctor_set(x_1507, 1, x_1506);
lean_ctor_set(x_1507, 2, x_1504);
x_1508 = lean_box(0);
x_1509 = 0;
x_1510 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1510, 0, x_1507);
lean_ctor_set(x_1510, 1, x_1482);
lean_ctor_set(x_1510, 2, x_1508);
lean_ctor_set_uint8(x_1510, sizeof(void*)*3, x_1509);
x_1511 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1511, 0, x_1510);
x_1512 = l_Lean_Core_getEnv___rarg(x_6, x_1505);
x_1513 = lean_ctor_get(x_1512, 0);
lean_inc(x_1513);
x_1514 = lean_ctor_get(x_1512, 1);
lean_inc(x_1514);
lean_dec(x_1512);
x_1515 = l_Lean_Options_empty;
x_1516 = l_Lean_Environment_addAndCompile(x_1513, x_1515, x_1511);
lean_dec(x_1511);
if (lean_obj_tag(x_1516) == 0)
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; uint8_t x_1524; 
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1449);
lean_dec(x_1442);
lean_dec(x_1);
x_1517 = lean_ctor_get(x_1516, 0);
lean_inc(x_1517);
lean_dec(x_1516);
x_1518 = l_Lean_KernelException_toMessageData(x_1517, x_1515);
x_1519 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1518);
x_1520 = l_Lean_Format_pretty(x_1519, x_1515);
x_1521 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1521, 0, x_1520);
x_1522 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1522, 0, x_1521);
x_1523 = l_Lean_Meta_throwError___rarg(x_1522, x_3, x_4, x_5, x_6, x_1514);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1524 = !lean_is_exclusive(x_1523);
if (x_1524 == 0)
{
return x_1523;
}
else
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; 
x_1525 = lean_ctor_get(x_1523, 0);
x_1526 = lean_ctor_get(x_1523, 1);
lean_inc(x_1526);
lean_inc(x_1525);
lean_dec(x_1523);
x_1527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1527, 0, x_1525);
lean_ctor_set(x_1527, 1, x_1526);
return x_1527;
}
}
else
{
lean_object* x_1528; 
x_1528 = lean_ctor_get(x_1516, 0);
lean_inc(x_1528);
lean_dec(x_1516);
x_1484 = x_1528;
x_1485 = x_1514;
goto block_1500;
}
}
else
{
uint8_t x_1529; 
lean_dec(x_1482);
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1449);
lean_dec(x_1442);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1529 = !lean_is_exclusive(x_1503);
if (x_1529 == 0)
{
return x_1503;
}
else
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
x_1530 = lean_ctor_get(x_1503, 0);
x_1531 = lean_ctor_get(x_1503, 1);
lean_inc(x_1531);
lean_inc(x_1530);
lean_dec(x_1503);
x_1532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1532, 0, x_1530);
lean_ctor_set(x_1532, 1, x_1531);
return x_1532;
}
}
block_1500:
{
lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
lean_inc(x_1456);
x_1486 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1454, x_1484, x_1442, x_1456);
x_1487 = l_Lean_Meta_setEnv(x_1486, x_3, x_4, x_5, x_6, x_1485);
x_1488 = lean_ctor_get(x_1487, 1);
lean_inc(x_1488);
lean_dec(x_1487);
x_1489 = lean_box(0);
x_1490 = l_Lean_mkConst(x_1456, x_1489);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1490);
x_1491 = l_Lean_Meta_inferType(x_1490, x_3, x_4, x_5, x_6, x_1488);
if (lean_obj_tag(x_1491) == 0)
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
x_1492 = lean_ctor_get(x_1491, 0);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1491, 1);
lean_inc(x_1493);
lean_dec(x_1491);
x_1494 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed), 11, 4);
lean_closure_set(x_1494, 0, x_1);
lean_closure_set(x_1494, 1, x_1461);
lean_closure_set(x_1494, 2, x_1449);
lean_closure_set(x_1494, 3, x_1490);
x_1495 = l_Lean_Meta_forallTelescope___rarg(x_1492, x_1494, x_3, x_4, x_5, x_6, x_1493);
return x_1495;
}
else
{
uint8_t x_1496; 
lean_dec(x_1490);
lean_dec(x_1449);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1496 = !lean_is_exclusive(x_1491);
if (x_1496 == 0)
{
return x_1491;
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1497 = lean_ctor_get(x_1491, 0);
x_1498 = lean_ctor_get(x_1491, 1);
lean_inc(x_1498);
lean_inc(x_1497);
lean_dec(x_1491);
x_1499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1499, 0, x_1497);
lean_ctor_set(x_1499, 1, x_1498);
return x_1499;
}
}
}
}
else
{
uint8_t x_1533; 
lean_dec(x_1460);
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1449);
lean_dec(x_1442);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1533 = !lean_is_exclusive(x_1481);
if (x_1533 == 0)
{
return x_1481;
}
else
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; 
x_1534 = lean_ctor_get(x_1481, 0);
x_1535 = lean_ctor_get(x_1481, 1);
lean_inc(x_1535);
lean_inc(x_1534);
lean_dec(x_1481);
x_1536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1536, 0, x_1534);
lean_ctor_set(x_1536, 1, x_1535);
return x_1536;
}
}
}
}
}
else
{
uint8_t x_1566; 
lean_dec(x_1460);
lean_dec(x_1458);
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1453);
lean_dec(x_1449);
lean_dec(x_1442);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1566 = !lean_is_exclusive(x_1462);
if (x_1566 == 0)
{
return x_1462;
}
else
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1567 = lean_ctor_get(x_1462, 0);
x_1568 = lean_ctor_get(x_1462, 1);
lean_inc(x_1568);
lean_inc(x_1567);
lean_dec(x_1462);
x_1569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1569, 0, x_1567);
lean_ctor_set(x_1569, 1, x_1568);
return x_1569;
}
}
}
else
{
uint8_t x_1570; 
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1453);
lean_dec(x_1449);
lean_dec(x_1442);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1570 = !lean_is_exclusive(x_1457);
if (x_1570 == 0)
{
return x_1457;
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
x_1571 = lean_ctor_get(x_1457, 0);
x_1572 = lean_ctor_get(x_1457, 1);
lean_inc(x_1572);
lean_inc(x_1571);
lean_dec(x_1457);
x_1573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1573, 0, x_1571);
lean_ctor_set(x_1573, 1, x_1572);
return x_1573;
}
}
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
lean_dec(x_1454);
lean_dec(x_1453);
lean_dec(x_1442);
lean_dec(x_9);
x_1574 = lean_ctor_get(x_1455, 0);
lean_inc(x_1574);
lean_dec(x_1455);
x_1575 = lean_box(0);
x_1576 = l_Lean_mkConst(x_1574, x_1575);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1576);
x_1577 = l_Lean_Meta_inferType(x_1576, x_3, x_4, x_5, x_6, x_1452);
if (lean_obj_tag(x_1577) == 0)
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
x_1578 = lean_ctor_get(x_1577, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1577, 1);
lean_inc(x_1579);
lean_dec(x_1577);
x_1580 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed), 10, 3);
lean_closure_set(x_1580, 0, x_1);
lean_closure_set(x_1580, 1, x_1449);
lean_closure_set(x_1580, 2, x_1576);
x_1581 = l_Lean_Meta_forallTelescope___rarg(x_1578, x_1580, x_3, x_4, x_5, x_6, x_1579);
return x_1581;
}
else
{
uint8_t x_1582; 
lean_dec(x_1576);
lean_dec(x_1449);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1582 = !lean_is_exclusive(x_1577);
if (x_1582 == 0)
{
return x_1577;
}
else
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; 
x_1583 = lean_ctor_get(x_1577, 0);
x_1584 = lean_ctor_get(x_1577, 1);
lean_inc(x_1584);
lean_inc(x_1583);
lean_dec(x_1577);
x_1585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1585, 0, x_1583);
lean_ctor_set(x_1585, 1, x_1584);
return x_1585;
}
}
}
}
else
{
lean_object* x_1586; 
lean_dec(x_1431);
lean_dec(x_1);
x_1586 = lean_box(0);
x_1432 = x_1586;
goto block_1441;
}
block_1441:
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_1432);
x_1433 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1434 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1434, 0, x_1433);
x_1435 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1435, 0, x_1434);
x_1436 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1437 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1437, 0, x_1436);
lean_ctor_set(x_1437, 1, x_1435);
x_1438 = l_Lean_Core_getConstInfo___closed__5;
x_1439 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1439, 0, x_1437);
lean_ctor_set(x_1439, 1, x_1438);
x_1440 = l_Lean_Meta_throwError___rarg(x_1439, x_3, x_4, x_5, x_6, x_1430);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1440;
}
}
default: 
{
lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; 
x_1587 = lean_ctor_get(x_8, 1);
lean_inc(x_1587);
lean_dec(x_8);
x_1588 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_1588) == 4)
{
lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; 
x_1599 = lean_ctor_get(x_1588, 0);
lean_inc(x_1599);
lean_dec(x_1588);
x_1600 = lean_unsigned_to_nat(0u);
x_1601 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_1600);
x_1602 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1601);
x_1603 = lean_mk_array(x_1601, x_1602);
x_1604 = lean_unsigned_to_nat(1u);
x_1605 = lean_nat_sub(x_1601, x_1604);
lean_dec(x_1601);
lean_inc(x_9);
x_1606 = l___private_Lean_Expr_3__getAppArgsAux___main(x_9, x_1603, x_1605);
x_1607 = l_Lean_Core_getEnv___rarg(x_6, x_1587);
x_1608 = lean_ctor_get(x_1607, 0);
lean_inc(x_1608);
x_1609 = lean_ctor_get(x_1607, 1);
lean_inc(x_1609);
lean_dec(x_1607);
x_1610 = lean_ctor_get(x_1, 0);
lean_inc(x_1610);
x_1611 = lean_ctor_get(x_1, 2);
lean_inc(x_1611);
x_1612 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1611, x_1608, x_1599);
lean_dec(x_1608);
if (lean_obj_tag(x_1612) == 0)
{
lean_object* x_1613; lean_object* x_1614; 
lean_inc(x_1610);
x_1613 = l_Lean_Name_append___main(x_1599, x_1610);
lean_inc(x_1599);
x_1614 = l_Lean_Meta_getConstInfo(x_1599, x_3, x_4, x_5, x_6, x_1609);
if (lean_obj_tag(x_1614) == 0)
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; 
x_1615 = lean_ctor_get(x_1614, 0);
lean_inc(x_1615);
x_1616 = lean_ctor_get(x_1614, 1);
lean_inc(x_1616);
lean_dec(x_1614);
x_1617 = l_Lean_ConstantInfo_type(x_1615);
x_1618 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1617);
x_1619 = l_Lean_Meta_forallTelescope___rarg(x_1617, x_1618, x_3, x_4, x_5, x_6, x_1616);
if (lean_obj_tag(x_1619) == 0)
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1695; uint8_t x_1696; 
x_1620 = lean_ctor_get(x_1619, 0);
lean_inc(x_1620);
x_1621 = lean_ctor_get(x_1619, 1);
lean_inc(x_1621);
lean_dec(x_1619);
x_1695 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1696 = l_Lean_Expr_isConstOf(x_1620, x_1695);
if (x_1696 == 0)
{
lean_object* x_1697; uint8_t x_1698; 
x_1697 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1698 = l_Lean_Expr_isConstOf(x_1620, x_1697);
lean_dec(x_1620);
if (x_1698 == 0)
{
lean_object* x_1699; 
lean_dec(x_1617);
lean_dec(x_1615);
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1606);
lean_dec(x_1599);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1699 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_1621);
if (lean_obj_tag(x_1699) == 0)
{
lean_object* x_1700; 
x_1700 = lean_ctor_get(x_1699, 0);
lean_inc(x_1700);
if (lean_obj_tag(x_1700) == 0)
{
lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; 
lean_dec(x_1);
x_1701 = lean_ctor_get(x_1699, 1);
lean_inc(x_1701);
lean_dec(x_1699);
x_1702 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1702, 0, x_1610);
x_1703 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1704 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1704, 0, x_1703);
lean_ctor_set(x_1704, 1, x_1702);
x_1705 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1706 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1706, 0, x_1704);
lean_ctor_set(x_1706, 1, x_1705);
x_1707 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1708 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1708, 0, x_1707);
x_1709 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1709, 0, x_1708);
x_1710 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1710, 0, x_1706);
lean_ctor_set(x_1710, 1, x_1709);
x_1711 = l_Lean_Core_getConstInfo___closed__5;
x_1712 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1712, 0, x_1710);
lean_ctor_set(x_1712, 1, x_1711);
x_1713 = l_Lean_Meta_throwError___rarg(x_1712, x_3, x_4, x_5, x_6, x_1701);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1713;
}
else
{
lean_object* x_1714; lean_object* x_1715; 
lean_dec(x_1610);
lean_dec(x_9);
x_1714 = lean_ctor_get(x_1699, 1);
lean_inc(x_1714);
lean_dec(x_1699);
x_1715 = lean_ctor_get(x_1700, 0);
lean_inc(x_1715);
lean_dec(x_1700);
x_2 = x_1715;
x_7 = x_1714;
goto _start;
}
}
else
{
uint8_t x_1717; 
lean_dec(x_1610);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1717 = !lean_is_exclusive(x_1699);
if (x_1717 == 0)
{
return x_1699;
}
else
{
lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; 
x_1718 = lean_ctor_get(x_1699, 0);
x_1719 = lean_ctor_get(x_1699, 1);
lean_inc(x_1719);
lean_inc(x_1718);
lean_dec(x_1699);
x_1720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1720, 0, x_1718);
lean_ctor_set(x_1720, 1, x_1719);
return x_1720;
}
}
}
else
{
lean_object* x_1721; 
x_1721 = lean_box(0);
x_1622 = x_1721;
goto block_1694;
}
}
else
{
lean_object* x_1722; 
lean_dec(x_1620);
x_1722 = lean_box(0);
x_1622 = x_1722;
goto block_1694;
}
block_1694:
{
lean_object* x_1623; 
lean_dec(x_1622);
x_1623 = l_Lean_ConstantInfo_value_x3f(x_1615);
lean_dec(x_1615);
if (lean_obj_tag(x_1623) == 0)
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
lean_dec(x_1617);
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1606);
lean_dec(x_1599);
lean_dec(x_1);
x_1624 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1624, 0, x_1610);
x_1625 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1626 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1626, 0, x_1625);
lean_ctor_set(x_1626, 1, x_1624);
x_1627 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1628 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1628, 0, x_1626);
lean_ctor_set(x_1628, 1, x_1627);
x_1629 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1630 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1630, 0, x_1629);
x_1631 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1631, 0, x_1630);
x_1632 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1632, 0, x_1628);
lean_ctor_set(x_1632, 1, x_1631);
x_1633 = l_Lean_Core_getConstInfo___closed__5;
x_1634 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1634, 0, x_1632);
lean_ctor_set(x_1634, 1, x_1633);
x_1635 = l_Lean_Meta_throwError___rarg(x_1634, x_3, x_4, x_5, x_6, x_1621);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1635;
}
else
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
lean_dec(x_1610);
lean_dec(x_9);
x_1636 = lean_ctor_get(x_1623, 0);
lean_inc(x_1636);
lean_dec(x_1623);
x_1637 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1636);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_1638 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1637, x_3, x_4, x_5, x_6, x_1621);
if (lean_obj_tag(x_1638) == 0)
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; 
x_1639 = lean_ctor_get(x_1638, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1638, 1);
lean_inc(x_1640);
lean_dec(x_1638);
x_1658 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1659 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed), 9, 2);
lean_closure_set(x_1659, 0, x_1);
lean_closure_set(x_1659, 1, x_1658);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1660 = l_Lean_Meta_forallTelescope___rarg(x_1617, x_1659, x_3, x_4, x_5, x_6, x_1640);
if (lean_obj_tag(x_1660) == 0)
{
lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; uint8_t x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1661 = lean_ctor_get(x_1660, 0);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1660, 1);
lean_inc(x_1662);
lean_dec(x_1660);
x_1663 = lean_box(0);
lean_inc(x_1613);
x_1664 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1664, 0, x_1613);
lean_ctor_set(x_1664, 1, x_1663);
lean_ctor_set(x_1664, 2, x_1661);
x_1665 = lean_box(0);
x_1666 = 0;
x_1667 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1667, 0, x_1664);
lean_ctor_set(x_1667, 1, x_1639);
lean_ctor_set(x_1667, 2, x_1665);
lean_ctor_set_uint8(x_1667, sizeof(void*)*3, x_1666);
x_1668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1668, 0, x_1667);
x_1669 = l_Lean_Core_getEnv___rarg(x_6, x_1662);
x_1670 = lean_ctor_get(x_1669, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1669, 1);
lean_inc(x_1671);
lean_dec(x_1669);
x_1672 = l_Lean_Options_empty;
x_1673 = l_Lean_Environment_addAndCompile(x_1670, x_1672, x_1668);
lean_dec(x_1668);
if (lean_obj_tag(x_1673) == 0)
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; uint8_t x_1681; 
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1606);
lean_dec(x_1599);
lean_dec(x_1);
x_1674 = lean_ctor_get(x_1673, 0);
lean_inc(x_1674);
lean_dec(x_1673);
x_1675 = l_Lean_KernelException_toMessageData(x_1674, x_1672);
x_1676 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1675);
x_1677 = l_Lean_Format_pretty(x_1676, x_1672);
x_1678 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1678, 0, x_1677);
x_1679 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1679, 0, x_1678);
x_1680 = l_Lean_Meta_throwError___rarg(x_1679, x_3, x_4, x_5, x_6, x_1671);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1681 = !lean_is_exclusive(x_1680);
if (x_1681 == 0)
{
return x_1680;
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
x_1682 = lean_ctor_get(x_1680, 0);
x_1683 = lean_ctor_get(x_1680, 1);
lean_inc(x_1683);
lean_inc(x_1682);
lean_dec(x_1680);
x_1684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1684, 0, x_1682);
lean_ctor_set(x_1684, 1, x_1683);
return x_1684;
}
}
else
{
lean_object* x_1685; 
x_1685 = lean_ctor_get(x_1673, 0);
lean_inc(x_1685);
lean_dec(x_1673);
x_1641 = x_1685;
x_1642 = x_1671;
goto block_1657;
}
}
else
{
uint8_t x_1686; 
lean_dec(x_1639);
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1606);
lean_dec(x_1599);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1686 = !lean_is_exclusive(x_1660);
if (x_1686 == 0)
{
return x_1660;
}
else
{
lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1687 = lean_ctor_get(x_1660, 0);
x_1688 = lean_ctor_get(x_1660, 1);
lean_inc(x_1688);
lean_inc(x_1687);
lean_dec(x_1660);
x_1689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1689, 0, x_1687);
lean_ctor_set(x_1689, 1, x_1688);
return x_1689;
}
}
block_1657:
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
lean_inc(x_1613);
x_1643 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1611, x_1641, x_1599, x_1613);
x_1644 = l_Lean_Meta_setEnv(x_1643, x_3, x_4, x_5, x_6, x_1642);
x_1645 = lean_ctor_get(x_1644, 1);
lean_inc(x_1645);
lean_dec(x_1644);
x_1646 = lean_box(0);
x_1647 = l_Lean_mkConst(x_1613, x_1646);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1647);
x_1648 = l_Lean_Meta_inferType(x_1647, x_3, x_4, x_5, x_6, x_1645);
if (lean_obj_tag(x_1648) == 0)
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1648, 1);
lean_inc(x_1650);
lean_dec(x_1648);
x_1651 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed), 11, 4);
lean_closure_set(x_1651, 0, x_1);
lean_closure_set(x_1651, 1, x_1618);
lean_closure_set(x_1651, 2, x_1606);
lean_closure_set(x_1651, 3, x_1647);
x_1652 = l_Lean_Meta_forallTelescope___rarg(x_1649, x_1651, x_3, x_4, x_5, x_6, x_1650);
return x_1652;
}
else
{
uint8_t x_1653; 
lean_dec(x_1647);
lean_dec(x_1606);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1653 = !lean_is_exclusive(x_1648);
if (x_1653 == 0)
{
return x_1648;
}
else
{
lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
x_1654 = lean_ctor_get(x_1648, 0);
x_1655 = lean_ctor_get(x_1648, 1);
lean_inc(x_1655);
lean_inc(x_1654);
lean_dec(x_1648);
x_1656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1656, 0, x_1654);
lean_ctor_set(x_1656, 1, x_1655);
return x_1656;
}
}
}
}
else
{
uint8_t x_1690; 
lean_dec(x_1617);
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1606);
lean_dec(x_1599);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1690 = !lean_is_exclusive(x_1638);
if (x_1690 == 0)
{
return x_1638;
}
else
{
lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; 
x_1691 = lean_ctor_get(x_1638, 0);
x_1692 = lean_ctor_get(x_1638, 1);
lean_inc(x_1692);
lean_inc(x_1691);
lean_dec(x_1638);
x_1693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1693, 0, x_1691);
lean_ctor_set(x_1693, 1, x_1692);
return x_1693;
}
}
}
}
}
else
{
uint8_t x_1723; 
lean_dec(x_1617);
lean_dec(x_1615);
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_1606);
lean_dec(x_1599);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1723 = !lean_is_exclusive(x_1619);
if (x_1723 == 0)
{
return x_1619;
}
else
{
lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; 
x_1724 = lean_ctor_get(x_1619, 0);
x_1725 = lean_ctor_get(x_1619, 1);
lean_inc(x_1725);
lean_inc(x_1724);
lean_dec(x_1619);
x_1726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1726, 0, x_1724);
lean_ctor_set(x_1726, 1, x_1725);
return x_1726;
}
}
}
else
{
uint8_t x_1727; 
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_1606);
lean_dec(x_1599);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1727 = !lean_is_exclusive(x_1614);
if (x_1727 == 0)
{
return x_1614;
}
else
{
lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; 
x_1728 = lean_ctor_get(x_1614, 0);
x_1729 = lean_ctor_get(x_1614, 1);
lean_inc(x_1729);
lean_inc(x_1728);
lean_dec(x_1614);
x_1730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1730, 0, x_1728);
lean_ctor_set(x_1730, 1, x_1729);
return x_1730;
}
}
}
else
{
lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_1599);
lean_dec(x_9);
x_1731 = lean_ctor_get(x_1612, 0);
lean_inc(x_1731);
lean_dec(x_1612);
x_1732 = lean_box(0);
x_1733 = l_Lean_mkConst(x_1731, x_1732);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1733);
x_1734 = l_Lean_Meta_inferType(x_1733, x_3, x_4, x_5, x_6, x_1609);
if (lean_obj_tag(x_1734) == 0)
{
lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; 
x_1735 = lean_ctor_get(x_1734, 0);
lean_inc(x_1735);
x_1736 = lean_ctor_get(x_1734, 1);
lean_inc(x_1736);
lean_dec(x_1734);
x_1737 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed), 10, 3);
lean_closure_set(x_1737, 0, x_1);
lean_closure_set(x_1737, 1, x_1606);
lean_closure_set(x_1737, 2, x_1733);
x_1738 = l_Lean_Meta_forallTelescope___rarg(x_1735, x_1737, x_3, x_4, x_5, x_6, x_1736);
return x_1738;
}
else
{
uint8_t x_1739; 
lean_dec(x_1733);
lean_dec(x_1606);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1739 = !lean_is_exclusive(x_1734);
if (x_1739 == 0)
{
return x_1734;
}
else
{
lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; 
x_1740 = lean_ctor_get(x_1734, 0);
x_1741 = lean_ctor_get(x_1734, 1);
lean_inc(x_1741);
lean_inc(x_1740);
lean_dec(x_1734);
x_1742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1742, 0, x_1740);
lean_ctor_set(x_1742, 1, x_1741);
return x_1742;
}
}
}
}
else
{
lean_object* x_1743; 
lean_dec(x_1588);
lean_dec(x_1);
x_1743 = lean_box(0);
x_1589 = x_1743;
goto block_1598;
}
block_1598:
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
lean_dec(x_1589);
x_1590 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_1591 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1591, 0, x_1590);
x_1592 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1592, 0, x_1591);
x_1593 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1594 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1594, 0, x_1593);
lean_ctor_set(x_1594, 1, x_1592);
x_1595 = l_Lean_Core_getConstInfo___closed__5;
x_1596 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1596, 0, x_1594);
lean_ctor_set(x_1596, 1, x_1595);
x_1597 = l_Lean_Meta_throwError___rarg(x_1596, x_3, x_4, x_5, x_6, x_1587);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1597;
}
}
}
}
else
{
uint8_t x_1744; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1744 = !lean_is_exclusive(x_8);
if (x_1744 == 0)
{
return x_8;
}
else
{
lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; 
x_1745 = lean_ctor_get(x_8, 0);
x_1746 = lean_ctor_get(x_8, 1);
lean_inc(x_1746);
lean_inc(x_1745);
lean_dec(x_8);
x_1747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1747, 0, x_1745);
lean_ctor_set(x_1747, 1, x_1746);
return x_1747;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Exception_inhabited;
x_2 = lean_alloc_closure((void*)(l_Lean_Core_ECoreM_inhabited___rarg___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = l_Lean_mkConst(x_2, x_7);
x_9 = l_Lean_Core_getRef___rarg(x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_MetaM_toECoreM___rarg___closed__3;
x_13 = lean_io_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_MetaM_toECoreM___rarg___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
lean_inc(x_1);
x_17 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_8, x_16, x_14, x_4, x_5, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_ref_get(x_14, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_Core_getEnv___rarg(x_5, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_syntax_ident(x_2);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_nullKind;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
if (x_3 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
x_35 = lean_add_attribute(x_24, x_22, x_33, x_30, x_34, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Core_setEnv(x_36, x_4, x_5, x_37);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_41);
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = 1;
x_49 = lean_add_attribute(x_24, x_22, x_47, x_30, x_48, x_25);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Core_setEnv(x_50, x_4, x_5, x_51);
lean_dec(x_5);
lean_dec(x_4);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_dec(x_20);
x_60 = l_Lean_ParserCompiler_compileParser___rarg___closed__1;
x_61 = l_unreachable_x21___rarg(x_60);
x_62 = lean_apply_3(x_61, x_4, x_5, x_59);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_17, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 2)
{
uint8_t x_64; 
lean_dec(x_10);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_17, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
lean_ctor_set(x_17, 0, x_66);
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_17);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_17, 0);
lean_dec(x_71);
x_72 = l_Lean_Meta_Exception_toMessageData(x_63);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_10);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_17, 0, x_73);
return x_17;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_dec(x_17);
x_75 = l_Lean_Meta_Exception_toMessageData(x_63);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_10);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
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
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Core_throwError___rarg(x_7, x_2, x_3, x_4);
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
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Core_throwError___rarg(x_7, x_2, x_3, x_4);
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
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Core_throwError___rarg(x_7, x_2, x_3, x_4);
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
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_Core_getConstInfo(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Core_getEnv___rarg(x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_14 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_17 = l_Lean_Expr_isConstOf(x_13, x_16);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_9);
x_18 = lean_eval_const(x_11, x_2);
lean_dec(x_2);
lean_dec(x_11);
x_19 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_18, x_3, x_4, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_4(x_22, x_20, x_3, x_4, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_28, x_11, x_2);
lean_dec(x_11);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; lean_object* x_31; 
lean_free_object(x_9);
x_30 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_30, x_3, x_4, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Core_getEnv___rarg(x_4, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Name_append___main(x_2, x_36);
lean_dec(x_2);
x_38 = lean_eval_const(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
x_39 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_38, x_3, x_4, x_35);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_45, x_11, x_2);
lean_dec(x_11);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; lean_object* x_48; 
lean_free_object(x_9);
x_47 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_47, x_3, x_4, x_12);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Core_getEnv___rarg(x_4, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Lean_Name_append___main(x_2, x_53);
lean_dec(x_2);
x_55 = lean_eval_const(x_51, x_54);
lean_dec(x_54);
lean_dec(x_51);
x_56 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_55, x_3, x_4, x_52);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
lean_dec(x_46);
lean_ctor_set(x_9, 0, x_61);
return x_9;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_9, 0);
x_63 = lean_ctor_get(x_9, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_9);
x_64 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_65 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_66 = l_Lean_Expr_isConstOf(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_68 = l_Lean_Expr_isConstOf(x_64, x_67);
lean_dec(x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_eval_const(x_62, x_2);
lean_dec(x_2);
lean_dec(x_62);
x_70 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_69, x_3, x_4, x_63);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 3);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_apply_4(x_73, x_71, x_3, x_4, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_79, x_62, x_2);
lean_dec(x_62);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; lean_object* x_82; 
x_81 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_81, x_3, x_4, x_63);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Core_getEnv___rarg(x_4, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
lean_dec(x_1);
x_88 = l_Lean_Name_append___main(x_2, x_87);
lean_dec(x_2);
x_89 = lean_eval_const(x_85, x_88);
lean_dec(x_88);
lean_dec(x_85);
x_90 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_89, x_3, x_4, x_86);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_93 = x_82;
} else {
 lean_dec_ref(x_82);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_80, 0);
lean_inc(x_95);
lean_dec(x_80);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_63);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_64);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
x_98 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_97, x_62, x_2);
lean_dec(x_62);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; lean_object* x_100; 
x_99 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_100 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_99, x_3, x_4, x_63);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Core_getEnv___rarg(x_4, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_1, 0);
lean_inc(x_105);
lean_dec(x_1);
x_106 = l_Lean_Name_append___main(x_2, x_105);
lean_dec(x_2);
x_107 = lean_eval_const(x_103, x_106);
lean_dec(x_106);
lean_dec(x_103);
x_108 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_107, x_3, x_4, x_104);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_111 = x_100;
} else {
 lean_dec_ref(x_100);
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
lean_object* x_113; lean_object* x_114; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_98, 0);
lean_inc(x_113);
lean_dec(x_98);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_63);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_6);
if (x_115 == 0)
{
return x_6;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_6, 0);
x_117 = lean_ctor_get(x_6, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_6);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
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
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_1, x_2, x_3, x_4);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Core_getEnv___rarg(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_9);
x_17 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_15, x_12, x_16);
lean_dec(x_15);
x_18 = l_Lean_Core_setEnv(x_17, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
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
x_23 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_23;
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
