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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__7;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__8;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__4;
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__2;
extern lean_object* l_IO_Error_Inhabited;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forM___at_IO_runMeta___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_run___rarg___closed__5;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21(lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__12;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_ParserCompiler_preprocessParserBody___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__2;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__11;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_Table_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main(lean_object*);
lean_object* l_Lean_ParserCompiler_preprocessParserBody(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object*);
lean_object* lean_add_attribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_Context_tyName___rarg___boxed(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_run___rarg___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
extern lean_object* l_Lean_defaultMaxRecDepth;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1(lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_mkAppStx___closed__3;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_Expr_isConstOf(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* _init_l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_2);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_2, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_28;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_17, x_8, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_7, x_31);
x_6 = x_19;
x_7 = x_33;
x_9 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
lean_inc(x_7);
x_19 = l_Lean_Meta_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_7);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_20, x_22, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_mkApp(x_6, x_16);
x_5 = x_18;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_30 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_16, x_7, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkApp(x_6, x_31);
x_5 = x_18;
x_6 = x_33;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_2 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_mkLambda(x_2, x_7, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_ParserCompiler_Context_tyName___rarg(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_array_get_size(x_3);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(x_2, x_3, x_9, x_3, x_10, lean_box(0), x_9, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(x_1, x_4, x_4, x_2, x_8, x_3, x_6, x_7);
return x_9;
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
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_21);
x_23 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
lean_inc(x_6);
x_27 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_24, x_26);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_30, x_28, x_20);
lean_dec(x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_inc(x_29);
x_32 = l_Lean_Name_append___main(x_20, x_29);
lean_inc(x_20);
x_33 = l_Lean_Meta_getConstInfo(x_20, x_3, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_ConstantInfo_type(x_34);
x_37 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_36);
x_38 = l_Lean_Meta_forallTelescope___rarg(x_36, x_37, x_3, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_114; uint8_t x_115; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_114 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_115 = l_Lean_Expr_isConstOf(x_39, x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_117 = l_Lean_Expr_isConstOf(x_39, x_116);
lean_dec(x_39);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_6);
x_118 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_40);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_1);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_121, 0, x_29);
x_122 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Core_getConstInfo___closed__5;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_box(0);
x_133 = l_Lean_Meta_throwOther___rarg(x_131, x_132, x_3, x_120);
lean_dec(x_3);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_29);
lean_dec(x_6);
x_134 = lean_ctor_get(x_118, 1);
lean_inc(x_134);
lean_dec(x_118);
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
lean_dec(x_119);
x_2 = x_135;
x_4 = x_134;
goto _start;
}
}
else
{
uint8_t x_137; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_118);
if (x_137 == 0)
{
return x_118;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_118, 0);
x_139 = lean_ctor_get(x_118, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_118);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; 
x_141 = lean_box(0);
x_41 = x_141;
goto block_113;
}
}
else
{
lean_object* x_142; 
lean_dec(x_39);
x_142 = lean_box(0);
x_41 = x_142;
goto block_113;
}
block_113:
{
lean_object* x_42; 
lean_dec(x_41);
x_42 = l_Lean_ConstantInfo_value_x3f(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_1);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_29);
x_44 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Core_getConstInfo___closed__5;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Meta_throwOther___rarg(x_53, x_54, x_3, x_40);
lean_dec(x_3);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_29);
lean_dec(x_6);
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
lean_dec(x_42);
x_57 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_56);
lean_inc(x_3);
lean_inc(x_1);
x_58 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_57, x_3, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_78 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_79 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed), 6, 2);
lean_closure_set(x_79, 0, x_1);
lean_closure_set(x_79, 1, x_78);
lean_inc(x_3);
x_80 = l_Lean_Meta_forallTelescope___rarg(x_36, x_79, x_3, x_60);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
lean_inc(x_32);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_32);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_81);
x_85 = lean_box(0);
x_86 = 0;
x_87 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_59);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = l_Lean_Options_empty;
x_91 = l_Lean_Environment_addAndCompile(x_89, x_90, x_88);
lean_dec(x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_1);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_KernelException_toMessageData(x_92, x_90);
x_94 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_93);
x_95 = l_Lean_Format_pretty(x_94, x_90);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_box(0);
x_99 = l_Lean_Meta_throwOther___rarg(x_97, x_98, x_3, x_82);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_91, 0);
lean_inc(x_104);
lean_dec(x_91);
x_61 = x_104;
x_62 = x_82;
goto block_77;
}
}
else
{
uint8_t x_105; 
lean_dec(x_59);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_80);
if (x_105 == 0)
{
return x_80;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_80, 0);
x_107 = lean_ctor_get(x_80, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_80);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
block_77:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_32);
x_63 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_30, x_61, x_20, x_32);
x_64 = l_Lean_Meta_setEnv(x_63, x_3, x_62);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = l_Lean_mkConst(x_32, x_66);
lean_inc(x_3);
lean_inc(x_67);
x_68 = l_Lean_Meta_inferType(x_67, x_3, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed), 8, 4);
lean_closure_set(x_71, 0, x_1);
lean_closure_set(x_71, 1, x_37);
lean_closure_set(x_71, 2, x_27);
lean_closure_set(x_71, 3, x_67);
x_72 = l_Lean_Meta_forallTelescope___rarg(x_69, x_71, x_3, x_70);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_67);
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 0);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_68);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_58);
if (x_109 == 0)
{
return x_58;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_58, 0);
x_111 = lean_ctor_get(x_58, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_58);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_38);
if (x_143 == 0)
{
return x_38;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_38, 0);
x_145 = lean_ctor_get(x_38, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_38);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_33);
if (x_147 == 0)
{
return x_33;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_33, 0);
x_149 = lean_ctor_get(x_33, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_33);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_6);
x_151 = lean_ctor_get(x_31, 0);
lean_inc(x_151);
lean_dec(x_31);
x_152 = lean_box(0);
x_153 = l_Lean_mkConst(x_151, x_152);
lean_inc(x_3);
lean_inc(x_153);
x_154 = l_Lean_Meta_inferType(x_153, x_3, x_7);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed), 7, 3);
lean_closure_set(x_157, 0, x_1);
lean_closure_set(x_157, 1, x_27);
lean_closure_set(x_157, 2, x_153);
x_158 = l_Lean_Meta_forallTelescope___rarg(x_155, x_157, x_3, x_156);
return x_158;
}
else
{
uint8_t x_159; 
lean_dec(x_153);
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_154);
if (x_159 == 0)
{
return x_154;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_154, 0);
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_154);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_8);
lean_dec(x_1);
x_163 = lean_box(0);
x_9 = x_163;
goto block_19;
}
block_19:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_10 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Core_getConstInfo___closed__5;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwOther___rarg(x_16, x_17, x_3, x_7);
lean_dec(x_3);
return x_18;
}
}
case 1:
{
uint8_t x_164; 
lean_dec(x_3);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_5);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_5, 0);
lean_dec(x_165);
return x_5;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_5, 1);
lean_inc(x_166);
lean_dec(x_5);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_6);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
case 2:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_5, 1);
lean_inc(x_168);
lean_dec(x_5);
x_169 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_169) == 4)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_181 = lean_ctor_get(x_169, 0);
lean_inc(x_181);
lean_dec(x_169);
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_182);
x_184 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_183);
x_185 = lean_mk_array(x_183, x_184);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_sub(x_183, x_186);
lean_dec(x_183);
lean_inc(x_6);
x_188 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_185, x_187);
x_189 = lean_ctor_get(x_168, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_1, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_1, 2);
lean_inc(x_191);
x_192 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_191, x_189, x_181);
lean_dec(x_189);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_inc(x_190);
x_193 = l_Lean_Name_append___main(x_181, x_190);
lean_inc(x_181);
x_194 = l_Lean_Meta_getConstInfo(x_181, x_3, x_168);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = l_Lean_ConstantInfo_type(x_195);
x_198 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_197);
x_199 = l_Lean_Meta_forallTelescope___rarg(x_197, x_198, x_3, x_196);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_275; uint8_t x_276; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_275 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_276 = l_Lean_Expr_isConstOf(x_200, x_275);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_278 = l_Lean_Expr_isConstOf(x_200, x_277);
lean_dec(x_200);
if (x_278 == 0)
{
lean_object* x_279; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_188);
lean_dec(x_181);
lean_inc(x_3);
lean_inc(x_6);
x_279 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_201);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_1);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_282, 0, x_190);
x_283 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_284 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
x_285 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_286 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_290, 0, x_286);
lean_ctor_set(x_290, 1, x_289);
x_291 = l_Lean_Core_getConstInfo___closed__5;
x_292 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_box(0);
x_294 = l_Lean_Meta_throwOther___rarg(x_292, x_293, x_3, x_281);
lean_dec(x_3);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_190);
lean_dec(x_6);
x_295 = lean_ctor_get(x_279, 1);
lean_inc(x_295);
lean_dec(x_279);
x_296 = lean_ctor_get(x_280, 0);
lean_inc(x_296);
lean_dec(x_280);
x_2 = x_296;
x_4 = x_295;
goto _start;
}
}
else
{
uint8_t x_298; 
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_279);
if (x_298 == 0)
{
return x_279;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_279, 0);
x_300 = lean_ctor_get(x_279, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_279);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; 
x_302 = lean_box(0);
x_202 = x_302;
goto block_274;
}
}
else
{
lean_object* x_303; 
lean_dec(x_200);
x_303 = lean_box(0);
x_202 = x_303;
goto block_274;
}
block_274:
{
lean_object* x_203; 
lean_dec(x_202);
x_203 = l_Lean_ConstantInfo_value_x3f(x_195);
lean_dec(x_195);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_197);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_188);
lean_dec(x_181);
lean_dec(x_1);
x_204 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_204, 0, x_190);
x_205 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_206 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_208 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_212, 0, x_208);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Core_getConstInfo___closed__5;
x_214 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_box(0);
x_216 = l_Lean_Meta_throwOther___rarg(x_214, x_215, x_3, x_201);
lean_dec(x_3);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_190);
lean_dec(x_6);
x_217 = lean_ctor_get(x_203, 0);
lean_inc(x_217);
lean_dec(x_203);
x_218 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_217);
lean_inc(x_3);
lean_inc(x_1);
x_219 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_218, x_3, x_201);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_239 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_240 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed), 6, 2);
lean_closure_set(x_240, 0, x_1);
lean_closure_set(x_240, 1, x_239);
lean_inc(x_3);
x_241 = l_Lean_Meta_forallTelescope___rarg(x_197, x_240, x_3, x_221);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_box(0);
lean_inc(x_193);
x_245 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_245, 0, x_193);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set(x_245, 2, x_242);
x_246 = lean_box(0);
x_247 = 0;
x_248 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_220);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*3, x_247);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_ctor_get(x_243, 0);
lean_inc(x_250);
x_251 = l_Lean_Options_empty;
x_252 = l_Lean_Environment_addAndCompile(x_250, x_251, x_249);
lean_dec(x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_188);
lean_dec(x_181);
lean_dec(x_1);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lean_KernelException_toMessageData(x_253, x_251);
x_255 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_254);
x_256 = l_Lean_Format_pretty(x_255, x_251);
x_257 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_box(0);
x_260 = l_Lean_Meta_throwOther___rarg(x_258, x_259, x_3, x_243);
lean_dec(x_3);
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
return x_260;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_260, 0);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_260);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
else
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_252, 0);
lean_inc(x_265);
lean_dec(x_252);
x_222 = x_265;
x_223 = x_243;
goto block_238;
}
}
else
{
uint8_t x_266; 
lean_dec(x_220);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_188);
lean_dec(x_181);
lean_dec(x_3);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_241);
if (x_266 == 0)
{
return x_241;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_241, 0);
x_268 = lean_ctor_get(x_241, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_241);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
block_238:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_inc(x_193);
x_224 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_191, x_222, x_181, x_193);
x_225 = l_Lean_Meta_setEnv(x_224, x_3, x_223);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_box(0);
x_228 = l_Lean_mkConst(x_193, x_227);
lean_inc(x_3);
lean_inc(x_228);
x_229 = l_Lean_Meta_inferType(x_228, x_3, x_226);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed), 8, 4);
lean_closure_set(x_232, 0, x_1);
lean_closure_set(x_232, 1, x_198);
lean_closure_set(x_232, 2, x_188);
lean_closure_set(x_232, 3, x_228);
x_233 = l_Lean_Meta_forallTelescope___rarg(x_230, x_232, x_3, x_231);
return x_233;
}
else
{
uint8_t x_234; 
lean_dec(x_228);
lean_dec(x_188);
lean_dec(x_3);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_229);
if (x_234 == 0)
{
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_229);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_197);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_188);
lean_dec(x_181);
lean_dec(x_3);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_219);
if (x_270 == 0)
{
return x_219;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_219, 0);
x_272 = lean_ctor_get(x_219, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_219);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_181);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_199);
if (x_304 == 0)
{
return x_199;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_199, 0);
x_306 = lean_ctor_get(x_199, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_199);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_181);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_194);
if (x_308 == 0)
{
return x_194;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_194, 0);
x_310 = lean_ctor_get(x_194, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_194);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_181);
lean_dec(x_6);
x_312 = lean_ctor_get(x_192, 0);
lean_inc(x_312);
lean_dec(x_192);
x_313 = lean_box(0);
x_314 = l_Lean_mkConst(x_312, x_313);
lean_inc(x_3);
lean_inc(x_314);
x_315 = l_Lean_Meta_inferType(x_314, x_3, x_168);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed), 7, 3);
lean_closure_set(x_318, 0, x_1);
lean_closure_set(x_318, 1, x_188);
lean_closure_set(x_318, 2, x_314);
x_319 = l_Lean_Meta_forallTelescope___rarg(x_316, x_318, x_3, x_317);
return x_319;
}
else
{
uint8_t x_320; 
lean_dec(x_314);
lean_dec(x_188);
lean_dec(x_3);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_315);
if (x_320 == 0)
{
return x_315;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_315, 0);
x_322 = lean_ctor_get(x_315, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_315);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
}
else
{
lean_object* x_324; 
lean_dec(x_169);
lean_dec(x_1);
x_324 = lean_box(0);
x_170 = x_324;
goto block_180;
}
block_180:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_170);
x_171 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_172 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_175 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = l_Lean_Core_getConstInfo___closed__5;
x_177 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_box(0);
x_179 = l_Lean_Meta_throwOther___rarg(x_177, x_178, x_3, x_168);
lean_dec(x_3);
return x_179;
}
}
case 3:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_5, 1);
lean_inc(x_325);
lean_dec(x_5);
x_326 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_326) == 4)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_338 = lean_ctor_get(x_326, 0);
lean_inc(x_338);
lean_dec(x_326);
x_339 = lean_unsigned_to_nat(0u);
x_340 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_339);
x_341 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_340);
x_342 = lean_mk_array(x_340, x_341);
x_343 = lean_unsigned_to_nat(1u);
x_344 = lean_nat_sub(x_340, x_343);
lean_dec(x_340);
lean_inc(x_6);
x_345 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_342, x_344);
x_346 = lean_ctor_get(x_325, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_1, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_1, 2);
lean_inc(x_348);
x_349 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_348, x_346, x_338);
lean_dec(x_346);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_inc(x_347);
x_350 = l_Lean_Name_append___main(x_338, x_347);
lean_inc(x_338);
x_351 = l_Lean_Meta_getConstInfo(x_338, x_3, x_325);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Lean_ConstantInfo_type(x_352);
x_355 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_354);
x_356 = l_Lean_Meta_forallTelescope___rarg(x_354, x_355, x_3, x_353);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_432; uint8_t x_433; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_432 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_433 = l_Lean_Expr_isConstOf(x_357, x_432);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_435 = l_Lean_Expr_isConstOf(x_357, x_434);
lean_dec(x_357);
if (x_435 == 0)
{
lean_object* x_436; 
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_338);
lean_inc(x_3);
lean_inc(x_6);
x_436 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_358);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_1);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_439, 0, x_347);
x_440 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_441 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_439);
x_442 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_443 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_445 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_447 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_447, 0, x_443);
lean_ctor_set(x_447, 1, x_446);
x_448 = l_Lean_Core_getConstInfo___closed__5;
x_449 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_box(0);
x_451 = l_Lean_Meta_throwOther___rarg(x_449, x_450, x_3, x_438);
lean_dec(x_3);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_347);
lean_dec(x_6);
x_452 = lean_ctor_get(x_436, 1);
lean_inc(x_452);
lean_dec(x_436);
x_453 = lean_ctor_get(x_437, 0);
lean_inc(x_453);
lean_dec(x_437);
x_2 = x_453;
x_4 = x_452;
goto _start;
}
}
else
{
uint8_t x_455; 
lean_dec(x_347);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_455 = !lean_is_exclusive(x_436);
if (x_455 == 0)
{
return x_436;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_436, 0);
x_457 = lean_ctor_get(x_436, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_436);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
else
{
lean_object* x_459; 
x_459 = lean_box(0);
x_359 = x_459;
goto block_431;
}
}
else
{
lean_object* x_460; 
lean_dec(x_357);
x_460 = lean_box(0);
x_359 = x_460;
goto block_431;
}
block_431:
{
lean_object* x_360; 
lean_dec(x_359);
x_360 = l_Lean_ConstantInfo_value_x3f(x_352);
lean_dec(x_352);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_338);
lean_dec(x_1);
x_361 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_361, 0, x_347);
x_362 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_363 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_365 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_367 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_Core_getConstInfo___closed__5;
x_371 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_box(0);
x_373 = l_Lean_Meta_throwOther___rarg(x_371, x_372, x_3, x_358);
lean_dec(x_3);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_347);
lean_dec(x_6);
x_374 = lean_ctor_get(x_360, 0);
lean_inc(x_374);
lean_dec(x_360);
x_375 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_374);
lean_inc(x_3);
lean_inc(x_1);
x_376 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_375, x_3, x_358);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_396 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_397 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed), 6, 2);
lean_closure_set(x_397, 0, x_1);
lean_closure_set(x_397, 1, x_396);
lean_inc(x_3);
x_398 = l_Lean_Meta_forallTelescope___rarg(x_354, x_397, x_3, x_378);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_box(0);
lean_inc(x_350);
x_402 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_402, 0, x_350);
lean_ctor_set(x_402, 1, x_401);
lean_ctor_set(x_402, 2, x_399);
x_403 = lean_box(0);
x_404 = 0;
x_405 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_377);
lean_ctor_set(x_405, 2, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*3, x_404);
x_406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = lean_ctor_get(x_400, 0);
lean_inc(x_407);
x_408 = l_Lean_Options_empty;
x_409 = l_Lean_Environment_addAndCompile(x_407, x_408, x_406);
lean_dec(x_406);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_338);
lean_dec(x_1);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec(x_409);
x_411 = l_Lean_KernelException_toMessageData(x_410, x_408);
x_412 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_411);
x_413 = l_Lean_Format_pretty(x_412, x_408);
x_414 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_415, 0, x_414);
x_416 = lean_box(0);
x_417 = l_Lean_Meta_throwOther___rarg(x_415, x_416, x_3, x_400);
lean_dec(x_3);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
return x_417;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_417, 0);
x_420 = lean_ctor_get(x_417, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_417);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
else
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_409, 0);
lean_inc(x_422);
lean_dec(x_409);
x_379 = x_422;
x_380 = x_400;
goto block_395;
}
}
else
{
uint8_t x_423; 
lean_dec(x_377);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_338);
lean_dec(x_3);
lean_dec(x_1);
x_423 = !lean_is_exclusive(x_398);
if (x_423 == 0)
{
return x_398;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_398, 0);
x_425 = lean_ctor_get(x_398, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_398);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
block_395:
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_inc(x_350);
x_381 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_348, x_379, x_338, x_350);
x_382 = l_Lean_Meta_setEnv(x_381, x_3, x_380);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_box(0);
x_385 = l_Lean_mkConst(x_350, x_384);
lean_inc(x_3);
lean_inc(x_385);
x_386 = l_Lean_Meta_inferType(x_385, x_3, x_383);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed), 8, 4);
lean_closure_set(x_389, 0, x_1);
lean_closure_set(x_389, 1, x_355);
lean_closure_set(x_389, 2, x_345);
lean_closure_set(x_389, 3, x_385);
x_390 = l_Lean_Meta_forallTelescope___rarg(x_387, x_389, x_3, x_388);
return x_390;
}
else
{
uint8_t x_391; 
lean_dec(x_385);
lean_dec(x_345);
lean_dec(x_3);
lean_dec(x_1);
x_391 = !lean_is_exclusive(x_386);
if (x_391 == 0)
{
return x_386;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_386, 0);
x_393 = lean_ctor_get(x_386, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_386);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
}
else
{
uint8_t x_427; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_338);
lean_dec(x_3);
lean_dec(x_1);
x_427 = !lean_is_exclusive(x_376);
if (x_427 == 0)
{
return x_376;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_376, 0);
x_429 = lean_ctor_get(x_376, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_376);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_338);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_356);
if (x_461 == 0)
{
return x_356;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_356, 0);
x_463 = lean_ctor_get(x_356, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_356);
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
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_338);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_465 = !lean_is_exclusive(x_351);
if (x_465 == 0)
{
return x_351;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_351, 0);
x_467 = lean_ctor_get(x_351, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_351);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_338);
lean_dec(x_6);
x_469 = lean_ctor_get(x_349, 0);
lean_inc(x_469);
lean_dec(x_349);
x_470 = lean_box(0);
x_471 = l_Lean_mkConst(x_469, x_470);
lean_inc(x_3);
lean_inc(x_471);
x_472 = l_Lean_Meta_inferType(x_471, x_3, x_325);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed), 7, 3);
lean_closure_set(x_475, 0, x_1);
lean_closure_set(x_475, 1, x_345);
lean_closure_set(x_475, 2, x_471);
x_476 = l_Lean_Meta_forallTelescope___rarg(x_473, x_475, x_3, x_474);
return x_476;
}
else
{
uint8_t x_477; 
lean_dec(x_471);
lean_dec(x_345);
lean_dec(x_3);
lean_dec(x_1);
x_477 = !lean_is_exclusive(x_472);
if (x_477 == 0)
{
return x_472;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_472, 0);
x_479 = lean_ctor_get(x_472, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_472);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
}
else
{
lean_object* x_481; 
lean_dec(x_326);
lean_dec(x_1);
x_481 = lean_box(0);
x_327 = x_481;
goto block_337;
}
block_337:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_327);
x_328 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_329 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_329, 0, x_328);
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_331 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_332 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
x_333 = l_Lean_Core_getConstInfo___closed__5;
x_334 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_box(0);
x_336 = l_Lean_Meta_throwOther___rarg(x_334, x_335, x_3, x_325);
lean_dec(x_3);
return x_336;
}
}
case 4:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_5, 1);
lean_inc(x_482);
lean_dec(x_5);
x_483 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_483) == 4)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_495 = lean_ctor_get(x_483, 0);
lean_inc(x_495);
lean_dec(x_483);
x_496 = lean_unsigned_to_nat(0u);
x_497 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_496);
x_498 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_497);
x_499 = lean_mk_array(x_497, x_498);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_nat_sub(x_497, x_500);
lean_dec(x_497);
lean_inc(x_6);
x_502 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_499, x_501);
x_503 = lean_ctor_get(x_482, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_1, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_1, 2);
lean_inc(x_505);
x_506 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_505, x_503, x_495);
lean_dec(x_503);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; 
lean_inc(x_504);
x_507 = l_Lean_Name_append___main(x_495, x_504);
lean_inc(x_495);
x_508 = l_Lean_Meta_getConstInfo(x_495, x_3, x_482);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_Lean_ConstantInfo_type(x_509);
x_512 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_511);
x_513 = l_Lean_Meta_forallTelescope___rarg(x_511, x_512, x_3, x_510);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_589; uint8_t x_590; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_589 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_590 = l_Lean_Expr_isConstOf(x_514, x_589);
if (x_590 == 0)
{
lean_object* x_591; uint8_t x_592; 
x_591 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_592 = l_Lean_Expr_isConstOf(x_514, x_591);
lean_dec(x_514);
if (x_592 == 0)
{
lean_object* x_593; 
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_502);
lean_dec(x_495);
lean_inc(x_3);
lean_inc(x_6);
x_593 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_515);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_1);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec(x_593);
x_596 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_596, 0, x_504);
x_597 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_598 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_596);
x_599 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_600 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
x_601 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_602 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_602, 0, x_601);
x_603 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_603, 0, x_602);
x_604 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_604, 0, x_600);
lean_ctor_set(x_604, 1, x_603);
x_605 = l_Lean_Core_getConstInfo___closed__5;
x_606 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_box(0);
x_608 = l_Lean_Meta_throwOther___rarg(x_606, x_607, x_3, x_595);
lean_dec(x_3);
return x_608;
}
else
{
lean_object* x_609; lean_object* x_610; 
lean_dec(x_504);
lean_dec(x_6);
x_609 = lean_ctor_get(x_593, 1);
lean_inc(x_609);
lean_dec(x_593);
x_610 = lean_ctor_get(x_594, 0);
lean_inc(x_610);
lean_dec(x_594);
x_2 = x_610;
x_4 = x_609;
goto _start;
}
}
else
{
uint8_t x_612; 
lean_dec(x_504);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_612 = !lean_is_exclusive(x_593);
if (x_612 == 0)
{
return x_593;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_593, 0);
x_614 = lean_ctor_get(x_593, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_593);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
else
{
lean_object* x_616; 
x_616 = lean_box(0);
x_516 = x_616;
goto block_588;
}
}
else
{
lean_object* x_617; 
lean_dec(x_514);
x_617 = lean_box(0);
x_516 = x_617;
goto block_588;
}
block_588:
{
lean_object* x_517; 
lean_dec(x_516);
x_517 = l_Lean_ConstantInfo_value_x3f(x_509);
lean_dec(x_509);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_511);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_502);
lean_dec(x_495);
lean_dec(x_1);
x_518 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_518, 0, x_504);
x_519 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_520 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_518);
x_521 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_522 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_524 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_524, 0, x_523);
x_525 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_525, 0, x_524);
x_526 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_526, 0, x_522);
lean_ctor_set(x_526, 1, x_525);
x_527 = l_Lean_Core_getConstInfo___closed__5;
x_528 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_box(0);
x_530 = l_Lean_Meta_throwOther___rarg(x_528, x_529, x_3, x_515);
lean_dec(x_3);
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_504);
lean_dec(x_6);
x_531 = lean_ctor_get(x_517, 0);
lean_inc(x_531);
lean_dec(x_517);
x_532 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_531);
lean_inc(x_3);
lean_inc(x_1);
x_533 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_532, x_3, x_515);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_553 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_554 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed), 6, 2);
lean_closure_set(x_554, 0, x_1);
lean_closure_set(x_554, 1, x_553);
lean_inc(x_3);
x_555 = l_Lean_Meta_forallTelescope___rarg(x_511, x_554, x_3, x_535);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_box(0);
lean_inc(x_507);
x_559 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_559, 0, x_507);
lean_ctor_set(x_559, 1, x_558);
lean_ctor_set(x_559, 2, x_556);
x_560 = lean_box(0);
x_561 = 0;
x_562 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_562, 0, x_559);
lean_ctor_set(x_562, 1, x_534);
lean_ctor_set(x_562, 2, x_560);
lean_ctor_set_uint8(x_562, sizeof(void*)*3, x_561);
x_563 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_563, 0, x_562);
x_564 = lean_ctor_get(x_557, 0);
lean_inc(x_564);
x_565 = l_Lean_Options_empty;
x_566 = l_Lean_Environment_addAndCompile(x_564, x_565, x_563);
lean_dec(x_563);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_502);
lean_dec(x_495);
lean_dec(x_1);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
lean_dec(x_566);
x_568 = l_Lean_KernelException_toMessageData(x_567, x_565);
x_569 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_568);
x_570 = l_Lean_Format_pretty(x_569, x_565);
x_571 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_571, 0, x_570);
x_572 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_572, 0, x_571);
x_573 = lean_box(0);
x_574 = l_Lean_Meta_throwOther___rarg(x_572, x_573, x_3, x_557);
lean_dec(x_3);
x_575 = !lean_is_exclusive(x_574);
if (x_575 == 0)
{
return x_574;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_574, 0);
x_577 = lean_ctor_get(x_574, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_574);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
else
{
lean_object* x_579; 
x_579 = lean_ctor_get(x_566, 0);
lean_inc(x_579);
lean_dec(x_566);
x_536 = x_579;
x_537 = x_557;
goto block_552;
}
}
else
{
uint8_t x_580; 
lean_dec(x_534);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_502);
lean_dec(x_495);
lean_dec(x_3);
lean_dec(x_1);
x_580 = !lean_is_exclusive(x_555);
if (x_580 == 0)
{
return x_555;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_555, 0);
x_582 = lean_ctor_get(x_555, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_555);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
block_552:
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_inc(x_507);
x_538 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_505, x_536, x_495, x_507);
x_539 = l_Lean_Meta_setEnv(x_538, x_3, x_537);
x_540 = lean_ctor_get(x_539, 1);
lean_inc(x_540);
lean_dec(x_539);
x_541 = lean_box(0);
x_542 = l_Lean_mkConst(x_507, x_541);
lean_inc(x_3);
lean_inc(x_542);
x_543 = l_Lean_Meta_inferType(x_542, x_3, x_540);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed), 8, 4);
lean_closure_set(x_546, 0, x_1);
lean_closure_set(x_546, 1, x_512);
lean_closure_set(x_546, 2, x_502);
lean_closure_set(x_546, 3, x_542);
x_547 = l_Lean_Meta_forallTelescope___rarg(x_544, x_546, x_3, x_545);
return x_547;
}
else
{
uint8_t x_548; 
lean_dec(x_542);
lean_dec(x_502);
lean_dec(x_3);
lean_dec(x_1);
x_548 = !lean_is_exclusive(x_543);
if (x_548 == 0)
{
return x_543;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_543, 0);
x_550 = lean_ctor_get(x_543, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_543);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_511);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_502);
lean_dec(x_495);
lean_dec(x_3);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_533);
if (x_584 == 0)
{
return x_533;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_533, 0);
x_586 = lean_ctor_get(x_533, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_533);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
}
}
else
{
uint8_t x_618; 
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_495);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_618 = !lean_is_exclusive(x_513);
if (x_618 == 0)
{
return x_513;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_513, 0);
x_620 = lean_ctor_get(x_513, 1);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_513);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
}
else
{
uint8_t x_622; 
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_495);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_622 = !lean_is_exclusive(x_508);
if (x_622 == 0)
{
return x_508;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_508, 0);
x_624 = lean_ctor_get(x_508, 1);
lean_inc(x_624);
lean_inc(x_623);
lean_dec(x_508);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_495);
lean_dec(x_6);
x_626 = lean_ctor_get(x_506, 0);
lean_inc(x_626);
lean_dec(x_506);
x_627 = lean_box(0);
x_628 = l_Lean_mkConst(x_626, x_627);
lean_inc(x_3);
lean_inc(x_628);
x_629 = l_Lean_Meta_inferType(x_628, x_3, x_482);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed), 7, 3);
lean_closure_set(x_632, 0, x_1);
lean_closure_set(x_632, 1, x_502);
lean_closure_set(x_632, 2, x_628);
x_633 = l_Lean_Meta_forallTelescope___rarg(x_630, x_632, x_3, x_631);
return x_633;
}
else
{
uint8_t x_634; 
lean_dec(x_628);
lean_dec(x_502);
lean_dec(x_3);
lean_dec(x_1);
x_634 = !lean_is_exclusive(x_629);
if (x_634 == 0)
{
return x_629;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_629, 0);
x_636 = lean_ctor_get(x_629, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_629);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
}
else
{
lean_object* x_638; 
lean_dec(x_483);
lean_dec(x_1);
x_638 = lean_box(0);
x_484 = x_638;
goto block_494;
}
block_494:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_484);
x_485 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_486 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_486, 0, x_485);
x_487 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_489 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_487);
x_490 = l_Lean_Core_getConstInfo___closed__5;
x_491 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_box(0);
x_493 = l_Lean_Meta_throwOther___rarg(x_491, x_492, x_3, x_482);
lean_dec(x_3);
return x_493;
}
}
case 5:
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_5, 1);
lean_inc(x_639);
lean_dec(x_5);
x_640 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_640) == 4)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_652 = lean_ctor_get(x_640, 0);
lean_inc(x_652);
lean_dec(x_640);
x_653 = lean_unsigned_to_nat(0u);
x_654 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_653);
x_655 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_654);
x_656 = lean_mk_array(x_654, x_655);
x_657 = lean_unsigned_to_nat(1u);
x_658 = lean_nat_sub(x_654, x_657);
lean_dec(x_654);
lean_inc(x_6);
x_659 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_656, x_658);
x_660 = lean_ctor_get(x_639, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_1, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_1, 2);
lean_inc(x_662);
x_663 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_662, x_660, x_652);
lean_dec(x_660);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; 
lean_inc(x_661);
x_664 = l_Lean_Name_append___main(x_652, x_661);
lean_inc(x_652);
x_665 = l_Lean_Meta_getConstInfo(x_652, x_3, x_639);
if (lean_obj_tag(x_665) == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
x_668 = l_Lean_ConstantInfo_type(x_666);
x_669 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_668);
x_670 = l_Lean_Meta_forallTelescope___rarg(x_668, x_669, x_3, x_667);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_746; uint8_t x_747; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
x_746 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_747 = l_Lean_Expr_isConstOf(x_671, x_746);
if (x_747 == 0)
{
lean_object* x_748; uint8_t x_749; 
x_748 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_749 = l_Lean_Expr_isConstOf(x_671, x_748);
lean_dec(x_671);
if (x_749 == 0)
{
lean_object* x_750; 
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_659);
lean_dec(x_652);
lean_inc(x_3);
lean_inc(x_6);
x_750 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_672);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_1);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_753 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_753, 0, x_661);
x_754 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_755 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_753);
x_756 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_757 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
x_758 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_759 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_759, 0, x_758);
x_760 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_760, 0, x_759);
x_761 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_761, 0, x_757);
lean_ctor_set(x_761, 1, x_760);
x_762 = l_Lean_Core_getConstInfo___closed__5;
x_763 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_763, 0, x_761);
lean_ctor_set(x_763, 1, x_762);
x_764 = lean_box(0);
x_765 = l_Lean_Meta_throwOther___rarg(x_763, x_764, x_3, x_752);
lean_dec(x_3);
return x_765;
}
else
{
lean_object* x_766; lean_object* x_767; 
lean_dec(x_661);
lean_dec(x_6);
x_766 = lean_ctor_get(x_750, 1);
lean_inc(x_766);
lean_dec(x_750);
x_767 = lean_ctor_get(x_751, 0);
lean_inc(x_767);
lean_dec(x_751);
x_2 = x_767;
x_4 = x_766;
goto _start;
}
}
else
{
uint8_t x_769; 
lean_dec(x_661);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_750);
if (x_769 == 0)
{
return x_750;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_750, 0);
x_771 = lean_ctor_get(x_750, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_750);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
lean_object* x_773; 
x_773 = lean_box(0);
x_673 = x_773;
goto block_745;
}
}
else
{
lean_object* x_774; 
lean_dec(x_671);
x_774 = lean_box(0);
x_673 = x_774;
goto block_745;
}
block_745:
{
lean_object* x_674; 
lean_dec(x_673);
x_674 = l_Lean_ConstantInfo_value_x3f(x_666);
lean_dec(x_666);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_668);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_659);
lean_dec(x_652);
lean_dec(x_1);
x_675 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_675, 0, x_661);
x_676 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_677 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_675);
x_678 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_679 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
x_680 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_681 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_681, 0, x_680);
x_682 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_682, 0, x_681);
x_683 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_683, 0, x_679);
lean_ctor_set(x_683, 1, x_682);
x_684 = l_Lean_Core_getConstInfo___closed__5;
x_685 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_box(0);
x_687 = l_Lean_Meta_throwOther___rarg(x_685, x_686, x_3, x_672);
lean_dec(x_3);
return x_687;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_661);
lean_dec(x_6);
x_688 = lean_ctor_get(x_674, 0);
lean_inc(x_688);
lean_dec(x_674);
x_689 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_688);
lean_inc(x_3);
lean_inc(x_1);
x_690 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_689, x_3, x_672);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_710 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_711 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed), 6, 2);
lean_closure_set(x_711, 0, x_1);
lean_closure_set(x_711, 1, x_710);
lean_inc(x_3);
x_712 = l_Lean_Meta_forallTelescope___rarg(x_668, x_711, x_3, x_692);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_box(0);
lean_inc(x_664);
x_716 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_716, 0, x_664);
lean_ctor_set(x_716, 1, x_715);
lean_ctor_set(x_716, 2, x_713);
x_717 = lean_box(0);
x_718 = 0;
x_719 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_719, 0, x_716);
lean_ctor_set(x_719, 1, x_691);
lean_ctor_set(x_719, 2, x_717);
lean_ctor_set_uint8(x_719, sizeof(void*)*3, x_718);
x_720 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_720, 0, x_719);
x_721 = lean_ctor_get(x_714, 0);
lean_inc(x_721);
x_722 = l_Lean_Options_empty;
x_723 = l_Lean_Environment_addAndCompile(x_721, x_722, x_720);
lean_dec(x_720);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; uint8_t x_732; 
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_659);
lean_dec(x_652);
lean_dec(x_1);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
lean_dec(x_723);
x_725 = l_Lean_KernelException_toMessageData(x_724, x_722);
x_726 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_725);
x_727 = l_Lean_Format_pretty(x_726, x_722);
x_728 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_728, 0, x_727);
x_729 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_729, 0, x_728);
x_730 = lean_box(0);
x_731 = l_Lean_Meta_throwOther___rarg(x_729, x_730, x_3, x_714);
lean_dec(x_3);
x_732 = !lean_is_exclusive(x_731);
if (x_732 == 0)
{
return x_731;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_733 = lean_ctor_get(x_731, 0);
x_734 = lean_ctor_get(x_731, 1);
lean_inc(x_734);
lean_inc(x_733);
lean_dec(x_731);
x_735 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_735, 0, x_733);
lean_ctor_set(x_735, 1, x_734);
return x_735;
}
}
else
{
lean_object* x_736; 
x_736 = lean_ctor_get(x_723, 0);
lean_inc(x_736);
lean_dec(x_723);
x_693 = x_736;
x_694 = x_714;
goto block_709;
}
}
else
{
uint8_t x_737; 
lean_dec(x_691);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_659);
lean_dec(x_652);
lean_dec(x_3);
lean_dec(x_1);
x_737 = !lean_is_exclusive(x_712);
if (x_737 == 0)
{
return x_712;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_712, 0);
x_739 = lean_ctor_get(x_712, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_712);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
block_709:
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_inc(x_664);
x_695 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_662, x_693, x_652, x_664);
x_696 = l_Lean_Meta_setEnv(x_695, x_3, x_694);
x_697 = lean_ctor_get(x_696, 1);
lean_inc(x_697);
lean_dec(x_696);
x_698 = lean_box(0);
x_699 = l_Lean_mkConst(x_664, x_698);
lean_inc(x_3);
lean_inc(x_699);
x_700 = l_Lean_Meta_inferType(x_699, x_3, x_697);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed), 8, 4);
lean_closure_set(x_703, 0, x_1);
lean_closure_set(x_703, 1, x_669);
lean_closure_set(x_703, 2, x_659);
lean_closure_set(x_703, 3, x_699);
x_704 = l_Lean_Meta_forallTelescope___rarg(x_701, x_703, x_3, x_702);
return x_704;
}
else
{
uint8_t x_705; 
lean_dec(x_699);
lean_dec(x_659);
lean_dec(x_3);
lean_dec(x_1);
x_705 = !lean_is_exclusive(x_700);
if (x_705 == 0)
{
return x_700;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_700, 0);
x_707 = lean_ctor_get(x_700, 1);
lean_inc(x_707);
lean_inc(x_706);
lean_dec(x_700);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set(x_708, 1, x_707);
return x_708;
}
}
}
}
else
{
uint8_t x_741; 
lean_dec(x_668);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_659);
lean_dec(x_652);
lean_dec(x_3);
lean_dec(x_1);
x_741 = !lean_is_exclusive(x_690);
if (x_741 == 0)
{
return x_690;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_690, 0);
x_743 = lean_ctor_get(x_690, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_690);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
}
}
}
else
{
uint8_t x_775; 
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_659);
lean_dec(x_652);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_775 = !lean_is_exclusive(x_670);
if (x_775 == 0)
{
return x_670;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_776 = lean_ctor_get(x_670, 0);
x_777 = lean_ctor_get(x_670, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_670);
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_776);
lean_ctor_set(x_778, 1, x_777);
return x_778;
}
}
}
else
{
uint8_t x_779; 
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_659);
lean_dec(x_652);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_779 = !lean_is_exclusive(x_665);
if (x_779 == 0)
{
return x_665;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_665, 0);
x_781 = lean_ctor_get(x_665, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_665);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_652);
lean_dec(x_6);
x_783 = lean_ctor_get(x_663, 0);
lean_inc(x_783);
lean_dec(x_663);
x_784 = lean_box(0);
x_785 = l_Lean_mkConst(x_783, x_784);
lean_inc(x_3);
lean_inc(x_785);
x_786 = l_Lean_Meta_inferType(x_785, x_3, x_639);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_789 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed), 7, 3);
lean_closure_set(x_789, 0, x_1);
lean_closure_set(x_789, 1, x_659);
lean_closure_set(x_789, 2, x_785);
x_790 = l_Lean_Meta_forallTelescope___rarg(x_787, x_789, x_3, x_788);
return x_790;
}
else
{
uint8_t x_791; 
lean_dec(x_785);
lean_dec(x_659);
lean_dec(x_3);
lean_dec(x_1);
x_791 = !lean_is_exclusive(x_786);
if (x_791 == 0)
{
return x_786;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_786, 0);
x_793 = lean_ctor_get(x_786, 1);
lean_inc(x_793);
lean_inc(x_792);
lean_dec(x_786);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_792);
lean_ctor_set(x_794, 1, x_793);
return x_794;
}
}
}
}
else
{
lean_object* x_795; 
lean_dec(x_640);
lean_dec(x_1);
x_795 = lean_box(0);
x_641 = x_795;
goto block_651;
}
block_651:
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_641);
x_642 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_646 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
x_647 = l_Lean_Core_getConstInfo___closed__5;
x_648 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
x_649 = lean_box(0);
x_650 = l_Lean_Meta_throwOther___rarg(x_648, x_649, x_3, x_639);
lean_dec(x_3);
return x_650;
}
}
case 6:
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_5, 1);
lean_inc(x_796);
lean_dec(x_5);
x_797 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__16), 5, 1);
lean_closure_set(x_797, 0, x_1);
x_798 = l_Lean_Meta_lambdaTelescope___rarg(x_6, x_797, x_3, x_796);
return x_798;
}
case 7:
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_5, 1);
lean_inc(x_799);
lean_dec(x_5);
x_800 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_800) == 4)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_812 = lean_ctor_get(x_800, 0);
lean_inc(x_812);
lean_dec(x_800);
x_813 = lean_unsigned_to_nat(0u);
x_814 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_813);
x_815 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_814);
x_816 = lean_mk_array(x_814, x_815);
x_817 = lean_unsigned_to_nat(1u);
x_818 = lean_nat_sub(x_814, x_817);
lean_dec(x_814);
lean_inc(x_6);
x_819 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_816, x_818);
x_820 = lean_ctor_get(x_799, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_1, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_1, 2);
lean_inc(x_822);
x_823 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_822, x_820, x_812);
lean_dec(x_820);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; 
lean_inc(x_821);
x_824 = l_Lean_Name_append___main(x_812, x_821);
lean_inc(x_812);
x_825 = l_Lean_Meta_getConstInfo(x_812, x_3, x_799);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = l_Lean_ConstantInfo_type(x_826);
x_829 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_828);
x_830 = l_Lean_Meta_forallTelescope___rarg(x_828, x_829, x_3, x_827);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_906; uint8_t x_907; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_830, 1);
lean_inc(x_832);
lean_dec(x_830);
x_906 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_907 = l_Lean_Expr_isConstOf(x_831, x_906);
if (x_907 == 0)
{
lean_object* x_908; uint8_t x_909; 
x_908 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_909 = l_Lean_Expr_isConstOf(x_831, x_908);
lean_dec(x_831);
if (x_909 == 0)
{
lean_object* x_910; 
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_812);
lean_inc(x_3);
lean_inc(x_6);
x_910 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_832);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; 
x_911 = lean_ctor_get(x_910, 0);
lean_inc(x_911);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_1);
x_912 = lean_ctor_get(x_910, 1);
lean_inc(x_912);
lean_dec(x_910);
x_913 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_913, 0, x_821);
x_914 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_915 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_915, 0, x_914);
lean_ctor_set(x_915, 1, x_913);
x_916 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_917 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_917, 0, x_915);
lean_ctor_set(x_917, 1, x_916);
x_918 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_919 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_919, 0, x_918);
x_920 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_920, 0, x_919);
x_921 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_921, 0, x_917);
lean_ctor_set(x_921, 1, x_920);
x_922 = l_Lean_Core_getConstInfo___closed__5;
x_923 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_923, 0, x_921);
lean_ctor_set(x_923, 1, x_922);
x_924 = lean_box(0);
x_925 = l_Lean_Meta_throwOther___rarg(x_923, x_924, x_3, x_912);
lean_dec(x_3);
return x_925;
}
else
{
lean_object* x_926; lean_object* x_927; 
lean_dec(x_821);
lean_dec(x_6);
x_926 = lean_ctor_get(x_910, 1);
lean_inc(x_926);
lean_dec(x_910);
x_927 = lean_ctor_get(x_911, 0);
lean_inc(x_927);
lean_dec(x_911);
x_2 = x_927;
x_4 = x_926;
goto _start;
}
}
else
{
uint8_t x_929; 
lean_dec(x_821);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_929 = !lean_is_exclusive(x_910);
if (x_929 == 0)
{
return x_910;
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_910, 0);
x_931 = lean_ctor_get(x_910, 1);
lean_inc(x_931);
lean_inc(x_930);
lean_dec(x_910);
x_932 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_931);
return x_932;
}
}
}
else
{
lean_object* x_933; 
x_933 = lean_box(0);
x_833 = x_933;
goto block_905;
}
}
else
{
lean_object* x_934; 
lean_dec(x_831);
x_934 = lean_box(0);
x_833 = x_934;
goto block_905;
}
block_905:
{
lean_object* x_834; 
lean_dec(x_833);
x_834 = l_Lean_ConstantInfo_value_x3f(x_826);
lean_dec(x_826);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_828);
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_812);
lean_dec(x_1);
x_835 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_835, 0, x_821);
x_836 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_837 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_835);
x_838 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_839 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set(x_839, 1, x_838);
x_840 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_841 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_841, 0, x_840);
x_842 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_842, 0, x_841);
x_843 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_843, 0, x_839);
lean_ctor_set(x_843, 1, x_842);
x_844 = l_Lean_Core_getConstInfo___closed__5;
x_845 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_844);
x_846 = lean_box(0);
x_847 = l_Lean_Meta_throwOther___rarg(x_845, x_846, x_3, x_832);
lean_dec(x_3);
return x_847;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_821);
lean_dec(x_6);
x_848 = lean_ctor_get(x_834, 0);
lean_inc(x_848);
lean_dec(x_834);
x_849 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_848);
lean_inc(x_3);
lean_inc(x_1);
x_850 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_849, x_3, x_832);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
lean_dec(x_850);
x_870 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_871 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed), 6, 2);
lean_closure_set(x_871, 0, x_1);
lean_closure_set(x_871, 1, x_870);
lean_inc(x_3);
x_872 = l_Lean_Meta_forallTelescope___rarg(x_828, x_871, x_3, x_852);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; uint8_t x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_box(0);
lean_inc(x_824);
x_876 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_876, 0, x_824);
lean_ctor_set(x_876, 1, x_875);
lean_ctor_set(x_876, 2, x_873);
x_877 = lean_box(0);
x_878 = 0;
x_879 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_851);
lean_ctor_set(x_879, 2, x_877);
lean_ctor_set_uint8(x_879, sizeof(void*)*3, x_878);
x_880 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_880, 0, x_879);
x_881 = lean_ctor_get(x_874, 0);
lean_inc(x_881);
x_882 = l_Lean_Options_empty;
x_883 = l_Lean_Environment_addAndCompile(x_881, x_882, x_880);
lean_dec(x_880);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; 
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_812);
lean_dec(x_1);
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
lean_dec(x_883);
x_885 = l_Lean_KernelException_toMessageData(x_884, x_882);
x_886 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_885);
x_887 = l_Lean_Format_pretty(x_886, x_882);
x_888 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_888, 0, x_887);
x_889 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_889, 0, x_888);
x_890 = lean_box(0);
x_891 = l_Lean_Meta_throwOther___rarg(x_889, x_890, x_3, x_874);
lean_dec(x_3);
x_892 = !lean_is_exclusive(x_891);
if (x_892 == 0)
{
return x_891;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_893 = lean_ctor_get(x_891, 0);
x_894 = lean_ctor_get(x_891, 1);
lean_inc(x_894);
lean_inc(x_893);
lean_dec(x_891);
x_895 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_895, 0, x_893);
lean_ctor_set(x_895, 1, x_894);
return x_895;
}
}
else
{
lean_object* x_896; 
x_896 = lean_ctor_get(x_883, 0);
lean_inc(x_896);
lean_dec(x_883);
x_853 = x_896;
x_854 = x_874;
goto block_869;
}
}
else
{
uint8_t x_897; 
lean_dec(x_851);
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_812);
lean_dec(x_3);
lean_dec(x_1);
x_897 = !lean_is_exclusive(x_872);
if (x_897 == 0)
{
return x_872;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_872, 0);
x_899 = lean_ctor_get(x_872, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_872);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
block_869:
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_inc(x_824);
x_855 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_822, x_853, x_812, x_824);
x_856 = l_Lean_Meta_setEnv(x_855, x_3, x_854);
x_857 = lean_ctor_get(x_856, 1);
lean_inc(x_857);
lean_dec(x_856);
x_858 = lean_box(0);
x_859 = l_Lean_mkConst(x_824, x_858);
lean_inc(x_3);
lean_inc(x_859);
x_860 = l_Lean_Meta_inferType(x_859, x_3, x_857);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_863 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed), 8, 4);
lean_closure_set(x_863, 0, x_1);
lean_closure_set(x_863, 1, x_829);
lean_closure_set(x_863, 2, x_819);
lean_closure_set(x_863, 3, x_859);
x_864 = l_Lean_Meta_forallTelescope___rarg(x_861, x_863, x_3, x_862);
return x_864;
}
else
{
uint8_t x_865; 
lean_dec(x_859);
lean_dec(x_819);
lean_dec(x_3);
lean_dec(x_1);
x_865 = !lean_is_exclusive(x_860);
if (x_865 == 0)
{
return x_860;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_866 = lean_ctor_get(x_860, 0);
x_867 = lean_ctor_get(x_860, 1);
lean_inc(x_867);
lean_inc(x_866);
lean_dec(x_860);
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_866);
lean_ctor_set(x_868, 1, x_867);
return x_868;
}
}
}
}
else
{
uint8_t x_901; 
lean_dec(x_828);
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_812);
lean_dec(x_3);
lean_dec(x_1);
x_901 = !lean_is_exclusive(x_850);
if (x_901 == 0)
{
return x_850;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_850, 0);
x_903 = lean_ctor_get(x_850, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_850);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
}
}
}
else
{
uint8_t x_935; 
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_819);
lean_dec(x_812);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_935 = !lean_is_exclusive(x_830);
if (x_935 == 0)
{
return x_830;
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_830, 0);
x_937 = lean_ctor_get(x_830, 1);
lean_inc(x_937);
lean_inc(x_936);
lean_dec(x_830);
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set(x_938, 1, x_937);
return x_938;
}
}
}
else
{
uint8_t x_939; 
lean_dec(x_824);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_819);
lean_dec(x_812);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_939 = !lean_is_exclusive(x_825);
if (x_939 == 0)
{
return x_825;
}
else
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_940 = lean_ctor_get(x_825, 0);
x_941 = lean_ctor_get(x_825, 1);
lean_inc(x_941);
lean_inc(x_940);
lean_dec(x_825);
x_942 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_942, 0, x_940);
lean_ctor_set(x_942, 1, x_941);
return x_942;
}
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_812);
lean_dec(x_6);
x_943 = lean_ctor_get(x_823, 0);
lean_inc(x_943);
lean_dec(x_823);
x_944 = lean_box(0);
x_945 = l_Lean_mkConst(x_943, x_944);
lean_inc(x_3);
lean_inc(x_945);
x_946 = l_Lean_Meta_inferType(x_945, x_3, x_799);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
lean_dec(x_946);
x_949 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed), 7, 3);
lean_closure_set(x_949, 0, x_1);
lean_closure_set(x_949, 1, x_819);
lean_closure_set(x_949, 2, x_945);
x_950 = l_Lean_Meta_forallTelescope___rarg(x_947, x_949, x_3, x_948);
return x_950;
}
else
{
uint8_t x_951; 
lean_dec(x_945);
lean_dec(x_819);
lean_dec(x_3);
lean_dec(x_1);
x_951 = !lean_is_exclusive(x_946);
if (x_951 == 0)
{
return x_946;
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_952 = lean_ctor_get(x_946, 0);
x_953 = lean_ctor_get(x_946, 1);
lean_inc(x_953);
lean_inc(x_952);
lean_dec(x_946);
x_954 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_954, 0, x_952);
lean_ctor_set(x_954, 1, x_953);
return x_954;
}
}
}
}
else
{
lean_object* x_955; 
lean_dec(x_800);
lean_dec(x_1);
x_955 = lean_box(0);
x_801 = x_955;
goto block_811;
}
block_811:
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_801);
x_802 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_803 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_803, 0, x_802);
x_804 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_804, 0, x_803);
x_805 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_806 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_806, 0, x_805);
lean_ctor_set(x_806, 1, x_804);
x_807 = l_Lean_Core_getConstInfo___closed__5;
x_808 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_808, 0, x_806);
lean_ctor_set(x_808, 1, x_807);
x_809 = lean_box(0);
x_810 = l_Lean_Meta_throwOther___rarg(x_808, x_809, x_3, x_799);
lean_dec(x_3);
return x_810;
}
}
case 8:
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_956 = lean_ctor_get(x_5, 1);
lean_inc(x_956);
lean_dec(x_5);
x_957 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_957) == 4)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_969 = lean_ctor_get(x_957, 0);
lean_inc(x_969);
lean_dec(x_957);
x_970 = lean_unsigned_to_nat(0u);
x_971 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_970);
x_972 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_971);
x_973 = lean_mk_array(x_971, x_972);
x_974 = lean_unsigned_to_nat(1u);
x_975 = lean_nat_sub(x_971, x_974);
lean_dec(x_971);
lean_inc(x_6);
x_976 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_973, x_975);
x_977 = lean_ctor_get(x_956, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_1, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_1, 2);
lean_inc(x_979);
x_980 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_979, x_977, x_969);
lean_dec(x_977);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; 
lean_inc(x_978);
x_981 = l_Lean_Name_append___main(x_969, x_978);
lean_inc(x_969);
x_982 = l_Lean_Meta_getConstInfo(x_969, x_3, x_956);
if (lean_obj_tag(x_982) == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
lean_dec(x_982);
x_985 = l_Lean_ConstantInfo_type(x_983);
x_986 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_985);
x_987 = l_Lean_Meta_forallTelescope___rarg(x_985, x_986, x_3, x_984);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_1063; uint8_t x_1064; 
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_987, 1);
lean_inc(x_989);
lean_dec(x_987);
x_1063 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1064 = l_Lean_Expr_isConstOf(x_988, x_1063);
if (x_1064 == 0)
{
lean_object* x_1065; uint8_t x_1066; 
x_1065 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1066 = l_Lean_Expr_isConstOf(x_988, x_1065);
lean_dec(x_988);
if (x_1066 == 0)
{
lean_object* x_1067; 
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_976);
lean_dec(x_969);
lean_inc(x_3);
lean_inc(x_6);
x_1067 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_989);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_1);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
lean_dec(x_1067);
x_1070 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1070, 0, x_978);
x_1071 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1072 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1072, 0, x_1071);
lean_ctor_set(x_1072, 1, x_1070);
x_1073 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1074 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1074, 0, x_1072);
lean_ctor_set(x_1074, 1, x_1073);
x_1075 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1076 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1076, 0, x_1075);
x_1077 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1077, 0, x_1076);
x_1078 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1078, 0, x_1074);
lean_ctor_set(x_1078, 1, x_1077);
x_1079 = l_Lean_Core_getConstInfo___closed__5;
x_1080 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1080, 0, x_1078);
lean_ctor_set(x_1080, 1, x_1079);
x_1081 = lean_box(0);
x_1082 = l_Lean_Meta_throwOther___rarg(x_1080, x_1081, x_3, x_1069);
lean_dec(x_3);
return x_1082;
}
else
{
lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_978);
lean_dec(x_6);
x_1083 = lean_ctor_get(x_1067, 1);
lean_inc(x_1083);
lean_dec(x_1067);
x_1084 = lean_ctor_get(x_1068, 0);
lean_inc(x_1084);
lean_dec(x_1068);
x_2 = x_1084;
x_4 = x_1083;
goto _start;
}
}
else
{
uint8_t x_1086; 
lean_dec(x_978);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1086 = !lean_is_exclusive(x_1067);
if (x_1086 == 0)
{
return x_1067;
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1087 = lean_ctor_get(x_1067, 0);
x_1088 = lean_ctor_get(x_1067, 1);
lean_inc(x_1088);
lean_inc(x_1087);
lean_dec(x_1067);
x_1089 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1089, 0, x_1087);
lean_ctor_set(x_1089, 1, x_1088);
return x_1089;
}
}
}
else
{
lean_object* x_1090; 
x_1090 = lean_box(0);
x_990 = x_1090;
goto block_1062;
}
}
else
{
lean_object* x_1091; 
lean_dec(x_988);
x_1091 = lean_box(0);
x_990 = x_1091;
goto block_1062;
}
block_1062:
{
lean_object* x_991; 
lean_dec(x_990);
x_991 = l_Lean_ConstantInfo_value_x3f(x_983);
lean_dec(x_983);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_985);
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_976);
lean_dec(x_969);
lean_dec(x_1);
x_992 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_992, 0, x_978);
x_993 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_994 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_994, 0, x_993);
lean_ctor_set(x_994, 1, x_992);
x_995 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_996 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_996, 0, x_994);
lean_ctor_set(x_996, 1, x_995);
x_997 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_998 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_998, 0, x_997);
x_999 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_999, 0, x_998);
x_1000 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1000, 0, x_996);
lean_ctor_set(x_1000, 1, x_999);
x_1001 = l_Lean_Core_getConstInfo___closed__5;
x_1002 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_box(0);
x_1004 = l_Lean_Meta_throwOther___rarg(x_1002, x_1003, x_3, x_989);
lean_dec(x_3);
return x_1004;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_978);
lean_dec(x_6);
x_1005 = lean_ctor_get(x_991, 0);
lean_inc(x_1005);
lean_dec(x_991);
x_1006 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1005);
lean_inc(x_3);
lean_inc(x_1);
x_1007 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1006, x_3, x_989);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
lean_dec(x_1007);
x_1027 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1028 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed), 6, 2);
lean_closure_set(x_1028, 0, x_1);
lean_closure_set(x_1028, 1, x_1027);
lean_inc(x_3);
x_1029 = l_Lean_Meta_forallTelescope___rarg(x_985, x_1028, x_3, x_1009);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = lean_box(0);
lean_inc(x_981);
x_1033 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1033, 0, x_981);
lean_ctor_set(x_1033, 1, x_1032);
lean_ctor_set(x_1033, 2, x_1030);
x_1034 = lean_box(0);
x_1035 = 0;
x_1036 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1036, 0, x_1033);
lean_ctor_set(x_1036, 1, x_1008);
lean_ctor_set(x_1036, 2, x_1034);
lean_ctor_set_uint8(x_1036, sizeof(void*)*3, x_1035);
x_1037 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1037, 0, x_1036);
x_1038 = lean_ctor_get(x_1031, 0);
lean_inc(x_1038);
x_1039 = l_Lean_Options_empty;
x_1040 = l_Lean_Environment_addAndCompile(x_1038, x_1039, x_1037);
lean_dec(x_1037);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; 
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_976);
lean_dec(x_969);
lean_dec(x_1);
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
lean_dec(x_1040);
x_1042 = l_Lean_KernelException_toMessageData(x_1041, x_1039);
x_1043 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1042);
x_1044 = l_Lean_Format_pretty(x_1043, x_1039);
x_1045 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1045, 0, x_1044);
x_1046 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1046, 0, x_1045);
x_1047 = lean_box(0);
x_1048 = l_Lean_Meta_throwOther___rarg(x_1046, x_1047, x_3, x_1031);
lean_dec(x_3);
x_1049 = !lean_is_exclusive(x_1048);
if (x_1049 == 0)
{
return x_1048;
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1050 = lean_ctor_get(x_1048, 0);
x_1051 = lean_ctor_get(x_1048, 1);
lean_inc(x_1051);
lean_inc(x_1050);
lean_dec(x_1048);
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1050);
lean_ctor_set(x_1052, 1, x_1051);
return x_1052;
}
}
else
{
lean_object* x_1053; 
x_1053 = lean_ctor_get(x_1040, 0);
lean_inc(x_1053);
lean_dec(x_1040);
x_1010 = x_1053;
x_1011 = x_1031;
goto block_1026;
}
}
else
{
uint8_t x_1054; 
lean_dec(x_1008);
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_976);
lean_dec(x_969);
lean_dec(x_3);
lean_dec(x_1);
x_1054 = !lean_is_exclusive(x_1029);
if (x_1054 == 0)
{
return x_1029;
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1055 = lean_ctor_get(x_1029, 0);
x_1056 = lean_ctor_get(x_1029, 1);
lean_inc(x_1056);
lean_inc(x_1055);
lean_dec(x_1029);
x_1057 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1057, 0, x_1055);
lean_ctor_set(x_1057, 1, x_1056);
return x_1057;
}
}
block_1026:
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
lean_inc(x_981);
x_1012 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_979, x_1010, x_969, x_981);
x_1013 = l_Lean_Meta_setEnv(x_1012, x_3, x_1011);
x_1014 = lean_ctor_get(x_1013, 1);
lean_inc(x_1014);
lean_dec(x_1013);
x_1015 = lean_box(0);
x_1016 = l_Lean_mkConst(x_981, x_1015);
lean_inc(x_3);
lean_inc(x_1016);
x_1017 = l_Lean_Meta_inferType(x_1016, x_3, x_1014);
if (lean_obj_tag(x_1017) == 0)
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed), 8, 4);
lean_closure_set(x_1020, 0, x_1);
lean_closure_set(x_1020, 1, x_986);
lean_closure_set(x_1020, 2, x_976);
lean_closure_set(x_1020, 3, x_1016);
x_1021 = l_Lean_Meta_forallTelescope___rarg(x_1018, x_1020, x_3, x_1019);
return x_1021;
}
else
{
uint8_t x_1022; 
lean_dec(x_1016);
lean_dec(x_976);
lean_dec(x_3);
lean_dec(x_1);
x_1022 = !lean_is_exclusive(x_1017);
if (x_1022 == 0)
{
return x_1017;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_1017, 0);
x_1024 = lean_ctor_get(x_1017, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_1017);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
}
else
{
uint8_t x_1058; 
lean_dec(x_985);
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_976);
lean_dec(x_969);
lean_dec(x_3);
lean_dec(x_1);
x_1058 = !lean_is_exclusive(x_1007);
if (x_1058 == 0)
{
return x_1007;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_1007, 0);
x_1060 = lean_ctor_get(x_1007, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_1007);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_1060);
return x_1061;
}
}
}
}
}
else
{
uint8_t x_1092; 
lean_dec(x_985);
lean_dec(x_983);
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_978);
lean_dec(x_976);
lean_dec(x_969);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1092 = !lean_is_exclusive(x_987);
if (x_1092 == 0)
{
return x_987;
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1093 = lean_ctor_get(x_987, 0);
x_1094 = lean_ctor_get(x_987, 1);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_987);
x_1095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1095, 0, x_1093);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
}
else
{
uint8_t x_1096; 
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_978);
lean_dec(x_976);
lean_dec(x_969);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1096 = !lean_is_exclusive(x_982);
if (x_1096 == 0)
{
return x_982;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_982, 0);
x_1098 = lean_ctor_get(x_982, 1);
lean_inc(x_1098);
lean_inc(x_1097);
lean_dec(x_982);
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_1097);
lean_ctor_set(x_1099, 1, x_1098);
return x_1099;
}
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_979);
lean_dec(x_978);
lean_dec(x_969);
lean_dec(x_6);
x_1100 = lean_ctor_get(x_980, 0);
lean_inc(x_1100);
lean_dec(x_980);
x_1101 = lean_box(0);
x_1102 = l_Lean_mkConst(x_1100, x_1101);
lean_inc(x_3);
lean_inc(x_1102);
x_1103 = l_Lean_Meta_inferType(x_1102, x_3, x_956);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1103, 1);
lean_inc(x_1105);
lean_dec(x_1103);
x_1106 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed), 7, 3);
lean_closure_set(x_1106, 0, x_1);
lean_closure_set(x_1106, 1, x_976);
lean_closure_set(x_1106, 2, x_1102);
x_1107 = l_Lean_Meta_forallTelescope___rarg(x_1104, x_1106, x_3, x_1105);
return x_1107;
}
else
{
uint8_t x_1108; 
lean_dec(x_1102);
lean_dec(x_976);
lean_dec(x_3);
lean_dec(x_1);
x_1108 = !lean_is_exclusive(x_1103);
if (x_1108 == 0)
{
return x_1103;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1109 = lean_ctor_get(x_1103, 0);
x_1110 = lean_ctor_get(x_1103, 1);
lean_inc(x_1110);
lean_inc(x_1109);
lean_dec(x_1103);
x_1111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
return x_1111;
}
}
}
}
else
{
lean_object* x_1112; 
lean_dec(x_957);
lean_dec(x_1);
x_1112 = lean_box(0);
x_958 = x_1112;
goto block_968;
}
block_968:
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
lean_dec(x_958);
x_959 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_960 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_960, 0, x_959);
x_961 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_961, 0, x_960);
x_962 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_963 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_963, 0, x_962);
lean_ctor_set(x_963, 1, x_961);
x_964 = l_Lean_Core_getConstInfo___closed__5;
x_965 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
x_966 = lean_box(0);
x_967 = l_Lean_Meta_throwOther___rarg(x_965, x_966, x_3, x_956);
lean_dec(x_3);
return x_967;
}
}
case 9:
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1113 = lean_ctor_get(x_5, 1);
lean_inc(x_1113);
lean_dec(x_5);
x_1114 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_1114) == 4)
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1126 = lean_ctor_get(x_1114, 0);
lean_inc(x_1126);
lean_dec(x_1114);
x_1127 = lean_unsigned_to_nat(0u);
x_1128 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_1127);
x_1129 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1128);
x_1130 = lean_mk_array(x_1128, x_1129);
x_1131 = lean_unsigned_to_nat(1u);
x_1132 = lean_nat_sub(x_1128, x_1131);
lean_dec(x_1128);
lean_inc(x_6);
x_1133 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_1130, x_1132);
x_1134 = lean_ctor_get(x_1113, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1, 2);
lean_inc(x_1136);
x_1137 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1136, x_1134, x_1126);
lean_dec(x_1134);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; lean_object* x_1139; 
lean_inc(x_1135);
x_1138 = l_Lean_Name_append___main(x_1126, x_1135);
lean_inc(x_1126);
x_1139 = l_Lean_Meta_getConstInfo(x_1126, x_3, x_1113);
if (lean_obj_tag(x_1139) == 0)
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1140 = lean_ctor_get(x_1139, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1139, 1);
lean_inc(x_1141);
lean_dec(x_1139);
x_1142 = l_Lean_ConstantInfo_type(x_1140);
x_1143 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_1142);
x_1144 = l_Lean_Meta_forallTelescope___rarg(x_1142, x_1143, x_3, x_1141);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1220; uint8_t x_1221; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
x_1220 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1221 = l_Lean_Expr_isConstOf(x_1145, x_1220);
if (x_1221 == 0)
{
lean_object* x_1222; uint8_t x_1223; 
x_1222 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1223 = l_Lean_Expr_isConstOf(x_1145, x_1222);
lean_dec(x_1145);
if (x_1223 == 0)
{
lean_object* x_1224; 
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1133);
lean_dec(x_1126);
lean_inc(x_3);
lean_inc(x_6);
x_1224 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_1146);
if (lean_obj_tag(x_1224) == 0)
{
lean_object* x_1225; 
x_1225 = lean_ctor_get(x_1224, 0);
lean_inc(x_1225);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1);
x_1226 = lean_ctor_get(x_1224, 1);
lean_inc(x_1226);
lean_dec(x_1224);
x_1227 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1227, 0, x_1135);
x_1228 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1229 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1229, 0, x_1228);
lean_ctor_set(x_1229, 1, x_1227);
x_1230 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1231 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1231, 0, x_1229);
lean_ctor_set(x_1231, 1, x_1230);
x_1232 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1233 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1233, 0, x_1232);
x_1234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1234, 0, x_1233);
x_1235 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1235, 0, x_1231);
lean_ctor_set(x_1235, 1, x_1234);
x_1236 = l_Lean_Core_getConstInfo___closed__5;
x_1237 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1237, 0, x_1235);
lean_ctor_set(x_1237, 1, x_1236);
x_1238 = lean_box(0);
x_1239 = l_Lean_Meta_throwOther___rarg(x_1237, x_1238, x_3, x_1226);
lean_dec(x_3);
return x_1239;
}
else
{
lean_object* x_1240; lean_object* x_1241; 
lean_dec(x_1135);
lean_dec(x_6);
x_1240 = lean_ctor_get(x_1224, 1);
lean_inc(x_1240);
lean_dec(x_1224);
x_1241 = lean_ctor_get(x_1225, 0);
lean_inc(x_1241);
lean_dec(x_1225);
x_2 = x_1241;
x_4 = x_1240;
goto _start;
}
}
else
{
uint8_t x_1243; 
lean_dec(x_1135);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1243 = !lean_is_exclusive(x_1224);
if (x_1243 == 0)
{
return x_1224;
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_ctor_get(x_1224, 0);
x_1245 = lean_ctor_get(x_1224, 1);
lean_inc(x_1245);
lean_inc(x_1244);
lean_dec(x_1224);
x_1246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1246, 0, x_1244);
lean_ctor_set(x_1246, 1, x_1245);
return x_1246;
}
}
}
else
{
lean_object* x_1247; 
x_1247 = lean_box(0);
x_1147 = x_1247;
goto block_1219;
}
}
else
{
lean_object* x_1248; 
lean_dec(x_1145);
x_1248 = lean_box(0);
x_1147 = x_1248;
goto block_1219;
}
block_1219:
{
lean_object* x_1148; 
lean_dec(x_1147);
x_1148 = l_Lean_ConstantInfo_value_x3f(x_1140);
lean_dec(x_1140);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_1142);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1133);
lean_dec(x_1126);
lean_dec(x_1);
x_1149 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1149, 0, x_1135);
x_1150 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1151 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1151, 0, x_1150);
lean_ctor_set(x_1151, 1, x_1149);
x_1152 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1153, 0, x_1151);
lean_ctor_set(x_1153, 1, x_1152);
x_1154 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1155, 0, x_1154);
x_1156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1156, 0, x_1155);
x_1157 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1157, 0, x_1153);
lean_ctor_set(x_1157, 1, x_1156);
x_1158 = l_Lean_Core_getConstInfo___closed__5;
x_1159 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
x_1160 = lean_box(0);
x_1161 = l_Lean_Meta_throwOther___rarg(x_1159, x_1160, x_3, x_1146);
lean_dec(x_3);
return x_1161;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1135);
lean_dec(x_6);
x_1162 = lean_ctor_get(x_1148, 0);
lean_inc(x_1162);
lean_dec(x_1148);
x_1163 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1162);
lean_inc(x_3);
lean_inc(x_1);
x_1164 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1163, x_3, x_1146);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
lean_dec(x_1164);
x_1184 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1185 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed), 6, 2);
lean_closure_set(x_1185, 0, x_1);
lean_closure_set(x_1185, 1, x_1184);
lean_inc(x_3);
x_1186 = l_Lean_Meta_forallTelescope___rarg(x_1142, x_1185, x_3, x_1166);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; uint8_t x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
x_1187 = lean_ctor_get(x_1186, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1186, 1);
lean_inc(x_1188);
lean_dec(x_1186);
x_1189 = lean_box(0);
lean_inc(x_1138);
x_1190 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1190, 0, x_1138);
lean_ctor_set(x_1190, 1, x_1189);
lean_ctor_set(x_1190, 2, x_1187);
x_1191 = lean_box(0);
x_1192 = 0;
x_1193 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1193, 0, x_1190);
lean_ctor_set(x_1193, 1, x_1165);
lean_ctor_set(x_1193, 2, x_1191);
lean_ctor_set_uint8(x_1193, sizeof(void*)*3, x_1192);
x_1194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1194, 0, x_1193);
x_1195 = lean_ctor_get(x_1188, 0);
lean_inc(x_1195);
x_1196 = l_Lean_Options_empty;
x_1197 = l_Lean_Environment_addAndCompile(x_1195, x_1196, x_1194);
lean_dec(x_1194);
if (lean_obj_tag(x_1197) == 0)
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; uint8_t x_1206; 
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1133);
lean_dec(x_1126);
lean_dec(x_1);
x_1198 = lean_ctor_get(x_1197, 0);
lean_inc(x_1198);
lean_dec(x_1197);
x_1199 = l_Lean_KernelException_toMessageData(x_1198, x_1196);
x_1200 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1199);
x_1201 = l_Lean_Format_pretty(x_1200, x_1196);
x_1202 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1202, 0, x_1201);
x_1203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1203, 0, x_1202);
x_1204 = lean_box(0);
x_1205 = l_Lean_Meta_throwOther___rarg(x_1203, x_1204, x_3, x_1188);
lean_dec(x_3);
x_1206 = !lean_is_exclusive(x_1205);
if (x_1206 == 0)
{
return x_1205;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1207 = lean_ctor_get(x_1205, 0);
x_1208 = lean_ctor_get(x_1205, 1);
lean_inc(x_1208);
lean_inc(x_1207);
lean_dec(x_1205);
x_1209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1209, 0, x_1207);
lean_ctor_set(x_1209, 1, x_1208);
return x_1209;
}
}
else
{
lean_object* x_1210; 
x_1210 = lean_ctor_get(x_1197, 0);
lean_inc(x_1210);
lean_dec(x_1197);
x_1167 = x_1210;
x_1168 = x_1188;
goto block_1183;
}
}
else
{
uint8_t x_1211; 
lean_dec(x_1165);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1133);
lean_dec(x_1126);
lean_dec(x_3);
lean_dec(x_1);
x_1211 = !lean_is_exclusive(x_1186);
if (x_1211 == 0)
{
return x_1186;
}
else
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
x_1212 = lean_ctor_get(x_1186, 0);
x_1213 = lean_ctor_get(x_1186, 1);
lean_inc(x_1213);
lean_inc(x_1212);
lean_dec(x_1186);
x_1214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1214, 0, x_1212);
lean_ctor_set(x_1214, 1, x_1213);
return x_1214;
}
}
block_1183:
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_inc(x_1138);
x_1169 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1136, x_1167, x_1126, x_1138);
x_1170 = l_Lean_Meta_setEnv(x_1169, x_3, x_1168);
x_1171 = lean_ctor_get(x_1170, 1);
lean_inc(x_1171);
lean_dec(x_1170);
x_1172 = lean_box(0);
x_1173 = l_Lean_mkConst(x_1138, x_1172);
lean_inc(x_3);
lean_inc(x_1173);
x_1174 = l_Lean_Meta_inferType(x_1173, x_3, x_1171);
if (lean_obj_tag(x_1174) == 0)
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1175 = lean_ctor_get(x_1174, 0);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1174, 1);
lean_inc(x_1176);
lean_dec(x_1174);
x_1177 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed), 8, 4);
lean_closure_set(x_1177, 0, x_1);
lean_closure_set(x_1177, 1, x_1143);
lean_closure_set(x_1177, 2, x_1133);
lean_closure_set(x_1177, 3, x_1173);
x_1178 = l_Lean_Meta_forallTelescope___rarg(x_1175, x_1177, x_3, x_1176);
return x_1178;
}
else
{
uint8_t x_1179; 
lean_dec(x_1173);
lean_dec(x_1133);
lean_dec(x_3);
lean_dec(x_1);
x_1179 = !lean_is_exclusive(x_1174);
if (x_1179 == 0)
{
return x_1174;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1174, 0);
x_1181 = lean_ctor_get(x_1174, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1174);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
}
}
else
{
uint8_t x_1215; 
lean_dec(x_1142);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1133);
lean_dec(x_1126);
lean_dec(x_3);
lean_dec(x_1);
x_1215 = !lean_is_exclusive(x_1164);
if (x_1215 == 0)
{
return x_1164;
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
x_1216 = lean_ctor_get(x_1164, 0);
x_1217 = lean_ctor_get(x_1164, 1);
lean_inc(x_1217);
lean_inc(x_1216);
lean_dec(x_1164);
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1216);
lean_ctor_set(x_1218, 1, x_1217);
return x_1218;
}
}
}
}
}
else
{
uint8_t x_1249; 
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1133);
lean_dec(x_1126);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1249 = !lean_is_exclusive(x_1144);
if (x_1249 == 0)
{
return x_1144;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
x_1250 = lean_ctor_get(x_1144, 0);
x_1251 = lean_ctor_get(x_1144, 1);
lean_inc(x_1251);
lean_inc(x_1250);
lean_dec(x_1144);
x_1252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1252, 0, x_1250);
lean_ctor_set(x_1252, 1, x_1251);
return x_1252;
}
}
}
else
{
uint8_t x_1253; 
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1133);
lean_dec(x_1126);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1253 = !lean_is_exclusive(x_1139);
if (x_1253 == 0)
{
return x_1139;
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1254 = lean_ctor_get(x_1139, 0);
x_1255 = lean_ctor_get(x_1139, 1);
lean_inc(x_1255);
lean_inc(x_1254);
lean_dec(x_1139);
x_1256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1256, 0, x_1254);
lean_ctor_set(x_1256, 1, x_1255);
return x_1256;
}
}
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1126);
lean_dec(x_6);
x_1257 = lean_ctor_get(x_1137, 0);
lean_inc(x_1257);
lean_dec(x_1137);
x_1258 = lean_box(0);
x_1259 = l_Lean_mkConst(x_1257, x_1258);
lean_inc(x_3);
lean_inc(x_1259);
x_1260 = l_Lean_Meta_inferType(x_1259, x_3, x_1113);
if (lean_obj_tag(x_1260) == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1261 = lean_ctor_get(x_1260, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1260, 1);
lean_inc(x_1262);
lean_dec(x_1260);
x_1263 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed), 7, 3);
lean_closure_set(x_1263, 0, x_1);
lean_closure_set(x_1263, 1, x_1133);
lean_closure_set(x_1263, 2, x_1259);
x_1264 = l_Lean_Meta_forallTelescope___rarg(x_1261, x_1263, x_3, x_1262);
return x_1264;
}
else
{
uint8_t x_1265; 
lean_dec(x_1259);
lean_dec(x_1133);
lean_dec(x_3);
lean_dec(x_1);
x_1265 = !lean_is_exclusive(x_1260);
if (x_1265 == 0)
{
return x_1260;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1266 = lean_ctor_get(x_1260, 0);
x_1267 = lean_ctor_get(x_1260, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1260);
x_1268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
return x_1268;
}
}
}
}
else
{
lean_object* x_1269; 
lean_dec(x_1114);
lean_dec(x_1);
x_1269 = lean_box(0);
x_1115 = x_1269;
goto block_1125;
}
block_1125:
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_1115);
x_1116 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1117, 0, x_1116);
x_1118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1118, 0, x_1117);
x_1119 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1120, 1, x_1118);
x_1121 = l_Lean_Core_getConstInfo___closed__5;
x_1122 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set(x_1122, 1, x_1121);
x_1123 = lean_box(0);
x_1124 = l_Lean_Meta_throwOther___rarg(x_1122, x_1123, x_3, x_1113);
lean_dec(x_3);
return x_1124;
}
}
case 10:
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = lean_ctor_get(x_5, 1);
lean_inc(x_1270);
lean_dec(x_5);
x_1271 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_1271) == 4)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1283 = lean_ctor_get(x_1271, 0);
lean_inc(x_1283);
lean_dec(x_1271);
x_1284 = lean_unsigned_to_nat(0u);
x_1285 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_1284);
x_1286 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1285);
x_1287 = lean_mk_array(x_1285, x_1286);
x_1288 = lean_unsigned_to_nat(1u);
x_1289 = lean_nat_sub(x_1285, x_1288);
lean_dec(x_1285);
lean_inc(x_6);
x_1290 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_1287, x_1289);
x_1291 = lean_ctor_get(x_1270, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1, 0);
lean_inc(x_1292);
x_1293 = lean_ctor_get(x_1, 2);
lean_inc(x_1293);
x_1294 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1293, x_1291, x_1283);
lean_dec(x_1291);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; lean_object* x_1296; 
lean_inc(x_1292);
x_1295 = l_Lean_Name_append___main(x_1283, x_1292);
lean_inc(x_1283);
x_1296 = l_Lean_Meta_getConstInfo(x_1283, x_3, x_1270);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1297 = lean_ctor_get(x_1296, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1296, 1);
lean_inc(x_1298);
lean_dec(x_1296);
x_1299 = l_Lean_ConstantInfo_type(x_1297);
x_1300 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_1299);
x_1301 = l_Lean_Meta_forallTelescope___rarg(x_1299, x_1300, x_3, x_1298);
if (lean_obj_tag(x_1301) == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1377; uint8_t x_1378; 
x_1302 = lean_ctor_get(x_1301, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1301, 1);
lean_inc(x_1303);
lean_dec(x_1301);
x_1377 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1378 = l_Lean_Expr_isConstOf(x_1302, x_1377);
if (x_1378 == 0)
{
lean_object* x_1379; uint8_t x_1380; 
x_1379 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1380 = l_Lean_Expr_isConstOf(x_1302, x_1379);
lean_dec(x_1302);
if (x_1380 == 0)
{
lean_object* x_1381; 
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1290);
lean_dec(x_1283);
lean_inc(x_3);
lean_inc(x_6);
x_1381 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_1303);
if (lean_obj_tag(x_1381) == 0)
{
lean_object* x_1382; 
x_1382 = lean_ctor_get(x_1381, 0);
lean_inc(x_1382);
if (lean_obj_tag(x_1382) == 0)
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_1);
x_1383 = lean_ctor_get(x_1381, 1);
lean_inc(x_1383);
lean_dec(x_1381);
x_1384 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1384, 0, x_1292);
x_1385 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1386 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1386, 0, x_1385);
lean_ctor_set(x_1386, 1, x_1384);
x_1387 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1388 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1388, 0, x_1386);
lean_ctor_set(x_1388, 1, x_1387);
x_1389 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1390 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1390, 0, x_1389);
x_1391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1391, 0, x_1390);
x_1392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1392, 0, x_1388);
lean_ctor_set(x_1392, 1, x_1391);
x_1393 = l_Lean_Core_getConstInfo___closed__5;
x_1394 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set(x_1394, 1, x_1393);
x_1395 = lean_box(0);
x_1396 = l_Lean_Meta_throwOther___rarg(x_1394, x_1395, x_3, x_1383);
lean_dec(x_3);
return x_1396;
}
else
{
lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1292);
lean_dec(x_6);
x_1397 = lean_ctor_get(x_1381, 1);
lean_inc(x_1397);
lean_dec(x_1381);
x_1398 = lean_ctor_get(x_1382, 0);
lean_inc(x_1398);
lean_dec(x_1382);
x_2 = x_1398;
x_4 = x_1397;
goto _start;
}
}
else
{
uint8_t x_1400; 
lean_dec(x_1292);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1400 = !lean_is_exclusive(x_1381);
if (x_1400 == 0)
{
return x_1381;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1381, 0);
x_1402 = lean_ctor_get(x_1381, 1);
lean_inc(x_1402);
lean_inc(x_1401);
lean_dec(x_1381);
x_1403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1403, 0, x_1401);
lean_ctor_set(x_1403, 1, x_1402);
return x_1403;
}
}
}
else
{
lean_object* x_1404; 
x_1404 = lean_box(0);
x_1304 = x_1404;
goto block_1376;
}
}
else
{
lean_object* x_1405; 
lean_dec(x_1302);
x_1405 = lean_box(0);
x_1304 = x_1405;
goto block_1376;
}
block_1376:
{
lean_object* x_1305; 
lean_dec(x_1304);
x_1305 = l_Lean_ConstantInfo_value_x3f(x_1297);
lean_dec(x_1297);
if (lean_obj_tag(x_1305) == 0)
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1299);
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1290);
lean_dec(x_1283);
lean_dec(x_1);
x_1306 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1306, 0, x_1292);
x_1307 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1308 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1308, 0, x_1307);
lean_ctor_set(x_1308, 1, x_1306);
x_1309 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1310 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1310, 0, x_1308);
lean_ctor_set(x_1310, 1, x_1309);
x_1311 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1312 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1312, 0, x_1311);
x_1313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1313, 0, x_1312);
x_1314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1314, 0, x_1310);
lean_ctor_set(x_1314, 1, x_1313);
x_1315 = l_Lean_Core_getConstInfo___closed__5;
x_1316 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1316, 0, x_1314);
lean_ctor_set(x_1316, 1, x_1315);
x_1317 = lean_box(0);
x_1318 = l_Lean_Meta_throwOther___rarg(x_1316, x_1317, x_3, x_1303);
lean_dec(x_3);
return x_1318;
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
lean_dec(x_1292);
lean_dec(x_6);
x_1319 = lean_ctor_get(x_1305, 0);
lean_inc(x_1319);
lean_dec(x_1305);
x_1320 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1319);
lean_inc(x_3);
lean_inc(x_1);
x_1321 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1320, x_3, x_1303);
if (lean_obj_tag(x_1321) == 0)
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
x_1323 = lean_ctor_get(x_1321, 1);
lean_inc(x_1323);
lean_dec(x_1321);
x_1341 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1342 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed), 6, 2);
lean_closure_set(x_1342, 0, x_1);
lean_closure_set(x_1342, 1, x_1341);
lean_inc(x_3);
x_1343 = l_Lean_Meta_forallTelescope___rarg(x_1299, x_1342, x_3, x_1323);
if (lean_obj_tag(x_1343) == 0)
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; uint8_t x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1344 = lean_ctor_get(x_1343, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1343, 1);
lean_inc(x_1345);
lean_dec(x_1343);
x_1346 = lean_box(0);
lean_inc(x_1295);
x_1347 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1347, 0, x_1295);
lean_ctor_set(x_1347, 1, x_1346);
lean_ctor_set(x_1347, 2, x_1344);
x_1348 = lean_box(0);
x_1349 = 0;
x_1350 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1350, 0, x_1347);
lean_ctor_set(x_1350, 1, x_1322);
lean_ctor_set(x_1350, 2, x_1348);
lean_ctor_set_uint8(x_1350, sizeof(void*)*3, x_1349);
x_1351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1351, 0, x_1350);
x_1352 = lean_ctor_get(x_1345, 0);
lean_inc(x_1352);
x_1353 = l_Lean_Options_empty;
x_1354 = l_Lean_Environment_addAndCompile(x_1352, x_1353, x_1351);
lean_dec(x_1351);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; uint8_t x_1363; 
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1290);
lean_dec(x_1283);
lean_dec(x_1);
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
lean_dec(x_1354);
x_1356 = l_Lean_KernelException_toMessageData(x_1355, x_1353);
x_1357 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1356);
x_1358 = l_Lean_Format_pretty(x_1357, x_1353);
x_1359 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1359, 0, x_1358);
x_1360 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1360, 0, x_1359);
x_1361 = lean_box(0);
x_1362 = l_Lean_Meta_throwOther___rarg(x_1360, x_1361, x_3, x_1345);
lean_dec(x_3);
x_1363 = !lean_is_exclusive(x_1362);
if (x_1363 == 0)
{
return x_1362;
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1364 = lean_ctor_get(x_1362, 0);
x_1365 = lean_ctor_get(x_1362, 1);
lean_inc(x_1365);
lean_inc(x_1364);
lean_dec(x_1362);
x_1366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1366, 0, x_1364);
lean_ctor_set(x_1366, 1, x_1365);
return x_1366;
}
}
else
{
lean_object* x_1367; 
x_1367 = lean_ctor_get(x_1354, 0);
lean_inc(x_1367);
lean_dec(x_1354);
x_1324 = x_1367;
x_1325 = x_1345;
goto block_1340;
}
}
else
{
uint8_t x_1368; 
lean_dec(x_1322);
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1290);
lean_dec(x_1283);
lean_dec(x_3);
lean_dec(x_1);
x_1368 = !lean_is_exclusive(x_1343);
if (x_1368 == 0)
{
return x_1343;
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = lean_ctor_get(x_1343, 0);
x_1370 = lean_ctor_get(x_1343, 1);
lean_inc(x_1370);
lean_inc(x_1369);
lean_dec(x_1343);
x_1371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1371, 0, x_1369);
lean_ctor_set(x_1371, 1, x_1370);
return x_1371;
}
}
block_1340:
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
lean_inc(x_1295);
x_1326 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1293, x_1324, x_1283, x_1295);
x_1327 = l_Lean_Meta_setEnv(x_1326, x_3, x_1325);
x_1328 = lean_ctor_get(x_1327, 1);
lean_inc(x_1328);
lean_dec(x_1327);
x_1329 = lean_box(0);
x_1330 = l_Lean_mkConst(x_1295, x_1329);
lean_inc(x_3);
lean_inc(x_1330);
x_1331 = l_Lean_Meta_inferType(x_1330, x_3, x_1328);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed), 8, 4);
lean_closure_set(x_1334, 0, x_1);
lean_closure_set(x_1334, 1, x_1300);
lean_closure_set(x_1334, 2, x_1290);
lean_closure_set(x_1334, 3, x_1330);
x_1335 = l_Lean_Meta_forallTelescope___rarg(x_1332, x_1334, x_3, x_1333);
return x_1335;
}
else
{
uint8_t x_1336; 
lean_dec(x_1330);
lean_dec(x_1290);
lean_dec(x_3);
lean_dec(x_1);
x_1336 = !lean_is_exclusive(x_1331);
if (x_1336 == 0)
{
return x_1331;
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; 
x_1337 = lean_ctor_get(x_1331, 0);
x_1338 = lean_ctor_get(x_1331, 1);
lean_inc(x_1338);
lean_inc(x_1337);
lean_dec(x_1331);
x_1339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1339, 0, x_1337);
lean_ctor_set(x_1339, 1, x_1338);
return x_1339;
}
}
}
}
else
{
uint8_t x_1372; 
lean_dec(x_1299);
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1290);
lean_dec(x_1283);
lean_dec(x_3);
lean_dec(x_1);
x_1372 = !lean_is_exclusive(x_1321);
if (x_1372 == 0)
{
return x_1321;
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1373 = lean_ctor_get(x_1321, 0);
x_1374 = lean_ctor_get(x_1321, 1);
lean_inc(x_1374);
lean_inc(x_1373);
lean_dec(x_1321);
x_1375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1375, 0, x_1373);
lean_ctor_set(x_1375, 1, x_1374);
return x_1375;
}
}
}
}
}
else
{
uint8_t x_1406; 
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1292);
lean_dec(x_1290);
lean_dec(x_1283);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1406 = !lean_is_exclusive(x_1301);
if (x_1406 == 0)
{
return x_1301;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
x_1407 = lean_ctor_get(x_1301, 0);
x_1408 = lean_ctor_get(x_1301, 1);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1301);
x_1409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1409, 0, x_1407);
lean_ctor_set(x_1409, 1, x_1408);
return x_1409;
}
}
}
else
{
uint8_t x_1410; 
lean_dec(x_1295);
lean_dec(x_1293);
lean_dec(x_1292);
lean_dec(x_1290);
lean_dec(x_1283);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1410 = !lean_is_exclusive(x_1296);
if (x_1410 == 0)
{
return x_1296;
}
else
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1411 = lean_ctor_get(x_1296, 0);
x_1412 = lean_ctor_get(x_1296, 1);
lean_inc(x_1412);
lean_inc(x_1411);
lean_dec(x_1296);
x_1413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1413, 0, x_1411);
lean_ctor_set(x_1413, 1, x_1412);
return x_1413;
}
}
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
lean_dec(x_1293);
lean_dec(x_1292);
lean_dec(x_1283);
lean_dec(x_6);
x_1414 = lean_ctor_get(x_1294, 0);
lean_inc(x_1414);
lean_dec(x_1294);
x_1415 = lean_box(0);
x_1416 = l_Lean_mkConst(x_1414, x_1415);
lean_inc(x_3);
lean_inc(x_1416);
x_1417 = l_Lean_Meta_inferType(x_1416, x_3, x_1270);
if (lean_obj_tag(x_1417) == 0)
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; 
x_1418 = lean_ctor_get(x_1417, 0);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1417, 1);
lean_inc(x_1419);
lean_dec(x_1417);
x_1420 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed), 7, 3);
lean_closure_set(x_1420, 0, x_1);
lean_closure_set(x_1420, 1, x_1290);
lean_closure_set(x_1420, 2, x_1416);
x_1421 = l_Lean_Meta_forallTelescope___rarg(x_1418, x_1420, x_3, x_1419);
return x_1421;
}
else
{
uint8_t x_1422; 
lean_dec(x_1416);
lean_dec(x_1290);
lean_dec(x_3);
lean_dec(x_1);
x_1422 = !lean_is_exclusive(x_1417);
if (x_1422 == 0)
{
return x_1417;
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
x_1423 = lean_ctor_get(x_1417, 0);
x_1424 = lean_ctor_get(x_1417, 1);
lean_inc(x_1424);
lean_inc(x_1423);
lean_dec(x_1417);
x_1425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1425, 0, x_1423);
lean_ctor_set(x_1425, 1, x_1424);
return x_1425;
}
}
}
}
else
{
lean_object* x_1426; 
lean_dec(x_1271);
lean_dec(x_1);
x_1426 = lean_box(0);
x_1272 = x_1426;
goto block_1282;
}
block_1282:
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; 
lean_dec(x_1272);
x_1273 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1274 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1274, 0, x_1273);
x_1275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1275, 0, x_1274);
x_1276 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1277 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1277, 0, x_1276);
lean_ctor_set(x_1277, 1, x_1275);
x_1278 = l_Lean_Core_getConstInfo___closed__5;
x_1279 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1279, 0, x_1277);
lean_ctor_set(x_1279, 1, x_1278);
x_1280 = lean_box(0);
x_1281 = l_Lean_Meta_throwOther___rarg(x_1279, x_1280, x_3, x_1270);
lean_dec(x_3);
return x_1281;
}
}
case 11:
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
x_1427 = lean_ctor_get(x_5, 1);
lean_inc(x_1427);
lean_dec(x_5);
x_1428 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_1428) == 4)
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
x_1440 = lean_ctor_get(x_1428, 0);
lean_inc(x_1440);
lean_dec(x_1428);
x_1441 = lean_unsigned_to_nat(0u);
x_1442 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_1441);
x_1443 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1442);
x_1444 = lean_mk_array(x_1442, x_1443);
x_1445 = lean_unsigned_to_nat(1u);
x_1446 = lean_nat_sub(x_1442, x_1445);
lean_dec(x_1442);
lean_inc(x_6);
x_1447 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_1444, x_1446);
x_1448 = lean_ctor_get(x_1427, 0);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1, 0);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1, 2);
lean_inc(x_1450);
x_1451 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1450, x_1448, x_1440);
lean_dec(x_1448);
if (lean_obj_tag(x_1451) == 0)
{
lean_object* x_1452; lean_object* x_1453; 
lean_inc(x_1449);
x_1452 = l_Lean_Name_append___main(x_1440, x_1449);
lean_inc(x_1440);
x_1453 = l_Lean_Meta_getConstInfo(x_1440, x_3, x_1427);
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1454 = lean_ctor_get(x_1453, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1453, 1);
lean_inc(x_1455);
lean_dec(x_1453);
x_1456 = l_Lean_ConstantInfo_type(x_1454);
x_1457 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_1456);
x_1458 = l_Lean_Meta_forallTelescope___rarg(x_1456, x_1457, x_3, x_1455);
if (lean_obj_tag(x_1458) == 0)
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1534; uint8_t x_1535; 
x_1459 = lean_ctor_get(x_1458, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1458, 1);
lean_inc(x_1460);
lean_dec(x_1458);
x_1534 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1535 = l_Lean_Expr_isConstOf(x_1459, x_1534);
if (x_1535 == 0)
{
lean_object* x_1536; uint8_t x_1537; 
x_1536 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1537 = l_Lean_Expr_isConstOf(x_1459, x_1536);
lean_dec(x_1459);
if (x_1537 == 0)
{
lean_object* x_1538; 
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1447);
lean_dec(x_1440);
lean_inc(x_3);
lean_inc(x_6);
x_1538 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_1460);
if (lean_obj_tag(x_1538) == 0)
{
lean_object* x_1539; 
x_1539 = lean_ctor_get(x_1538, 0);
lean_inc(x_1539);
if (lean_obj_tag(x_1539) == 0)
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
lean_dec(x_1);
x_1540 = lean_ctor_get(x_1538, 1);
lean_inc(x_1540);
lean_dec(x_1538);
x_1541 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1541, 0, x_1449);
x_1542 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1543 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1543, 0, x_1542);
lean_ctor_set(x_1543, 1, x_1541);
x_1544 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1545 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1545, 0, x_1543);
lean_ctor_set(x_1545, 1, x_1544);
x_1546 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1547 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1547, 0, x_1546);
x_1548 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1548, 0, x_1547);
x_1549 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1549, 0, x_1545);
lean_ctor_set(x_1549, 1, x_1548);
x_1550 = l_Lean_Core_getConstInfo___closed__5;
x_1551 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1551, 0, x_1549);
lean_ctor_set(x_1551, 1, x_1550);
x_1552 = lean_box(0);
x_1553 = l_Lean_Meta_throwOther___rarg(x_1551, x_1552, x_3, x_1540);
lean_dec(x_3);
return x_1553;
}
else
{
lean_object* x_1554; lean_object* x_1555; 
lean_dec(x_1449);
lean_dec(x_6);
x_1554 = lean_ctor_get(x_1538, 1);
lean_inc(x_1554);
lean_dec(x_1538);
x_1555 = lean_ctor_get(x_1539, 0);
lean_inc(x_1555);
lean_dec(x_1539);
x_2 = x_1555;
x_4 = x_1554;
goto _start;
}
}
else
{
uint8_t x_1557; 
lean_dec(x_1449);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1557 = !lean_is_exclusive(x_1538);
if (x_1557 == 0)
{
return x_1538;
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1558 = lean_ctor_get(x_1538, 0);
x_1559 = lean_ctor_get(x_1538, 1);
lean_inc(x_1559);
lean_inc(x_1558);
lean_dec(x_1538);
x_1560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1560, 0, x_1558);
lean_ctor_set(x_1560, 1, x_1559);
return x_1560;
}
}
}
else
{
lean_object* x_1561; 
x_1561 = lean_box(0);
x_1461 = x_1561;
goto block_1533;
}
}
else
{
lean_object* x_1562; 
lean_dec(x_1459);
x_1562 = lean_box(0);
x_1461 = x_1562;
goto block_1533;
}
block_1533:
{
lean_object* x_1462; 
lean_dec(x_1461);
x_1462 = l_Lean_ConstantInfo_value_x3f(x_1454);
lean_dec(x_1454);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
lean_dec(x_1456);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1447);
lean_dec(x_1440);
lean_dec(x_1);
x_1463 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1463, 0, x_1449);
x_1464 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1465 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1465, 0, x_1464);
lean_ctor_set(x_1465, 1, x_1463);
x_1466 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1467 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1467, 0, x_1465);
lean_ctor_set(x_1467, 1, x_1466);
x_1468 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1469 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1469, 0, x_1468);
x_1470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1470, 0, x_1469);
x_1471 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1471, 0, x_1467);
lean_ctor_set(x_1471, 1, x_1470);
x_1472 = l_Lean_Core_getConstInfo___closed__5;
x_1473 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1473, 0, x_1471);
lean_ctor_set(x_1473, 1, x_1472);
x_1474 = lean_box(0);
x_1475 = l_Lean_Meta_throwOther___rarg(x_1473, x_1474, x_3, x_1460);
lean_dec(x_3);
return x_1475;
}
else
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
lean_dec(x_1449);
lean_dec(x_6);
x_1476 = lean_ctor_get(x_1462, 0);
lean_inc(x_1476);
lean_dec(x_1462);
x_1477 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1476);
lean_inc(x_3);
lean_inc(x_1);
x_1478 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1477, x_3, x_1460);
if (lean_obj_tag(x_1478) == 0)
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
x_1479 = lean_ctor_get(x_1478, 0);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1478, 1);
lean_inc(x_1480);
lean_dec(x_1478);
x_1498 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1499 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed), 6, 2);
lean_closure_set(x_1499, 0, x_1);
lean_closure_set(x_1499, 1, x_1498);
lean_inc(x_3);
x_1500 = l_Lean_Meta_forallTelescope___rarg(x_1456, x_1499, x_3, x_1480);
if (lean_obj_tag(x_1500) == 0)
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1501 = lean_ctor_get(x_1500, 0);
lean_inc(x_1501);
x_1502 = lean_ctor_get(x_1500, 1);
lean_inc(x_1502);
lean_dec(x_1500);
x_1503 = lean_box(0);
lean_inc(x_1452);
x_1504 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1504, 0, x_1452);
lean_ctor_set(x_1504, 1, x_1503);
lean_ctor_set(x_1504, 2, x_1501);
x_1505 = lean_box(0);
x_1506 = 0;
x_1507 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1507, 0, x_1504);
lean_ctor_set(x_1507, 1, x_1479);
lean_ctor_set(x_1507, 2, x_1505);
lean_ctor_set_uint8(x_1507, sizeof(void*)*3, x_1506);
x_1508 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1508, 0, x_1507);
x_1509 = lean_ctor_get(x_1502, 0);
lean_inc(x_1509);
x_1510 = l_Lean_Options_empty;
x_1511 = l_Lean_Environment_addAndCompile(x_1509, x_1510, x_1508);
lean_dec(x_1508);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; uint8_t x_1520; 
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1447);
lean_dec(x_1440);
lean_dec(x_1);
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
lean_dec(x_1511);
x_1513 = l_Lean_KernelException_toMessageData(x_1512, x_1510);
x_1514 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1513);
x_1515 = l_Lean_Format_pretty(x_1514, x_1510);
x_1516 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1516, 0, x_1515);
x_1517 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1517, 0, x_1516);
x_1518 = lean_box(0);
x_1519 = l_Lean_Meta_throwOther___rarg(x_1517, x_1518, x_3, x_1502);
lean_dec(x_3);
x_1520 = !lean_is_exclusive(x_1519);
if (x_1520 == 0)
{
return x_1519;
}
else
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
x_1521 = lean_ctor_get(x_1519, 0);
x_1522 = lean_ctor_get(x_1519, 1);
lean_inc(x_1522);
lean_inc(x_1521);
lean_dec(x_1519);
x_1523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1523, 0, x_1521);
lean_ctor_set(x_1523, 1, x_1522);
return x_1523;
}
}
else
{
lean_object* x_1524; 
x_1524 = lean_ctor_get(x_1511, 0);
lean_inc(x_1524);
lean_dec(x_1511);
x_1481 = x_1524;
x_1482 = x_1502;
goto block_1497;
}
}
else
{
uint8_t x_1525; 
lean_dec(x_1479);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1447);
lean_dec(x_1440);
lean_dec(x_3);
lean_dec(x_1);
x_1525 = !lean_is_exclusive(x_1500);
if (x_1525 == 0)
{
return x_1500;
}
else
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1526 = lean_ctor_get(x_1500, 0);
x_1527 = lean_ctor_get(x_1500, 1);
lean_inc(x_1527);
lean_inc(x_1526);
lean_dec(x_1500);
x_1528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1528, 0, x_1526);
lean_ctor_set(x_1528, 1, x_1527);
return x_1528;
}
}
block_1497:
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
lean_inc(x_1452);
x_1483 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1450, x_1481, x_1440, x_1452);
x_1484 = l_Lean_Meta_setEnv(x_1483, x_3, x_1482);
x_1485 = lean_ctor_get(x_1484, 1);
lean_inc(x_1485);
lean_dec(x_1484);
x_1486 = lean_box(0);
x_1487 = l_Lean_mkConst(x_1452, x_1486);
lean_inc(x_3);
lean_inc(x_1487);
x_1488 = l_Lean_Meta_inferType(x_1487, x_3, x_1485);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; 
x_1489 = lean_ctor_get(x_1488, 0);
lean_inc(x_1489);
x_1490 = lean_ctor_get(x_1488, 1);
lean_inc(x_1490);
lean_dec(x_1488);
x_1491 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed), 8, 4);
lean_closure_set(x_1491, 0, x_1);
lean_closure_set(x_1491, 1, x_1457);
lean_closure_set(x_1491, 2, x_1447);
lean_closure_set(x_1491, 3, x_1487);
x_1492 = l_Lean_Meta_forallTelescope___rarg(x_1489, x_1491, x_3, x_1490);
return x_1492;
}
else
{
uint8_t x_1493; 
lean_dec(x_1487);
lean_dec(x_1447);
lean_dec(x_3);
lean_dec(x_1);
x_1493 = !lean_is_exclusive(x_1488);
if (x_1493 == 0)
{
return x_1488;
}
else
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
x_1494 = lean_ctor_get(x_1488, 0);
x_1495 = lean_ctor_get(x_1488, 1);
lean_inc(x_1495);
lean_inc(x_1494);
lean_dec(x_1488);
x_1496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1496, 0, x_1494);
lean_ctor_set(x_1496, 1, x_1495);
return x_1496;
}
}
}
}
else
{
uint8_t x_1529; 
lean_dec(x_1456);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1447);
lean_dec(x_1440);
lean_dec(x_3);
lean_dec(x_1);
x_1529 = !lean_is_exclusive(x_1478);
if (x_1529 == 0)
{
return x_1478;
}
else
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
x_1530 = lean_ctor_get(x_1478, 0);
x_1531 = lean_ctor_get(x_1478, 1);
lean_inc(x_1531);
lean_inc(x_1530);
lean_dec(x_1478);
x_1532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1532, 0, x_1530);
lean_ctor_set(x_1532, 1, x_1531);
return x_1532;
}
}
}
}
}
else
{
uint8_t x_1563; 
lean_dec(x_1456);
lean_dec(x_1454);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1447);
lean_dec(x_1440);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1563 = !lean_is_exclusive(x_1458);
if (x_1563 == 0)
{
return x_1458;
}
else
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; 
x_1564 = lean_ctor_get(x_1458, 0);
x_1565 = lean_ctor_get(x_1458, 1);
lean_inc(x_1565);
lean_inc(x_1564);
lean_dec(x_1458);
x_1566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1566, 0, x_1564);
lean_ctor_set(x_1566, 1, x_1565);
return x_1566;
}
}
}
else
{
uint8_t x_1567; 
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1447);
lean_dec(x_1440);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1567 = !lean_is_exclusive(x_1453);
if (x_1567 == 0)
{
return x_1453;
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1568 = lean_ctor_get(x_1453, 0);
x_1569 = lean_ctor_get(x_1453, 1);
lean_inc(x_1569);
lean_inc(x_1568);
lean_dec(x_1453);
x_1570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1570, 0, x_1568);
lean_ctor_set(x_1570, 1, x_1569);
return x_1570;
}
}
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; 
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1440);
lean_dec(x_6);
x_1571 = lean_ctor_get(x_1451, 0);
lean_inc(x_1571);
lean_dec(x_1451);
x_1572 = lean_box(0);
x_1573 = l_Lean_mkConst(x_1571, x_1572);
lean_inc(x_3);
lean_inc(x_1573);
x_1574 = l_Lean_Meta_inferType(x_1573, x_3, x_1427);
if (lean_obj_tag(x_1574) == 0)
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; 
x_1575 = lean_ctor_get(x_1574, 0);
lean_inc(x_1575);
x_1576 = lean_ctor_get(x_1574, 1);
lean_inc(x_1576);
lean_dec(x_1574);
x_1577 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed), 7, 3);
lean_closure_set(x_1577, 0, x_1);
lean_closure_set(x_1577, 1, x_1447);
lean_closure_set(x_1577, 2, x_1573);
x_1578 = l_Lean_Meta_forallTelescope___rarg(x_1575, x_1577, x_3, x_1576);
return x_1578;
}
else
{
uint8_t x_1579; 
lean_dec(x_1573);
lean_dec(x_1447);
lean_dec(x_3);
lean_dec(x_1);
x_1579 = !lean_is_exclusive(x_1574);
if (x_1579 == 0)
{
return x_1574;
}
else
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1580 = lean_ctor_get(x_1574, 0);
x_1581 = lean_ctor_get(x_1574, 1);
lean_inc(x_1581);
lean_inc(x_1580);
lean_dec(x_1574);
x_1582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1582, 0, x_1580);
lean_ctor_set(x_1582, 1, x_1581);
return x_1582;
}
}
}
}
else
{
lean_object* x_1583; 
lean_dec(x_1428);
lean_dec(x_1);
x_1583 = lean_box(0);
x_1429 = x_1583;
goto block_1439;
}
block_1439:
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
lean_dec(x_1429);
x_1430 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1431 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1431, 0, x_1430);
x_1432 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1432, 0, x_1431);
x_1433 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1434 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1434, 0, x_1433);
lean_ctor_set(x_1434, 1, x_1432);
x_1435 = l_Lean_Core_getConstInfo___closed__5;
x_1436 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1436, 0, x_1434);
lean_ctor_set(x_1436, 1, x_1435);
x_1437 = lean_box(0);
x_1438 = l_Lean_Meta_throwOther___rarg(x_1436, x_1437, x_3, x_1427);
lean_dec(x_3);
return x_1438;
}
}
default: 
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
x_1584 = lean_ctor_get(x_5, 1);
lean_inc(x_1584);
lean_dec(x_5);
x_1585 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_1585) == 4)
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
x_1597 = lean_ctor_get(x_1585, 0);
lean_inc(x_1597);
lean_dec(x_1585);
x_1598 = lean_unsigned_to_nat(0u);
x_1599 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_1598);
x_1600 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1599);
x_1601 = lean_mk_array(x_1599, x_1600);
x_1602 = lean_unsigned_to_nat(1u);
x_1603 = lean_nat_sub(x_1599, x_1602);
lean_dec(x_1599);
lean_inc(x_6);
x_1604 = l___private_Lean_Expr_3__getAppArgsAux___main(x_6, x_1601, x_1603);
x_1605 = lean_ctor_get(x_1584, 0);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1, 0);
lean_inc(x_1606);
x_1607 = lean_ctor_get(x_1, 2);
lean_inc(x_1607);
x_1608 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1607, x_1605, x_1597);
lean_dec(x_1605);
if (lean_obj_tag(x_1608) == 0)
{
lean_object* x_1609; lean_object* x_1610; 
lean_inc(x_1606);
x_1609 = l_Lean_Name_append___main(x_1597, x_1606);
lean_inc(x_1597);
x_1610 = l_Lean_Meta_getConstInfo(x_1597, x_3, x_1584);
if (lean_obj_tag(x_1610) == 0)
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; 
x_1611 = lean_ctor_get(x_1610, 0);
lean_inc(x_1611);
x_1612 = lean_ctor_get(x_1610, 1);
lean_inc(x_1612);
lean_dec(x_1610);
x_1613 = l_Lean_ConstantInfo_type(x_1611);
x_1614 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___closed__1;
lean_inc(x_3);
lean_inc(x_1613);
x_1615 = l_Lean_Meta_forallTelescope___rarg(x_1613, x_1614, x_3, x_1612);
if (lean_obj_tag(x_1615) == 0)
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1691; uint8_t x_1692; 
x_1616 = lean_ctor_get(x_1615, 0);
lean_inc(x_1616);
x_1617 = lean_ctor_get(x_1615, 1);
lean_inc(x_1617);
lean_dec(x_1615);
x_1691 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__10;
x_1692 = l_Lean_Expr_isConstOf(x_1616, x_1691);
if (x_1692 == 0)
{
lean_object* x_1693; uint8_t x_1694; 
x_1693 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_ParserCompiler_preprocessParserBody___spec__1___rarg___closed__1;
x_1694 = l_Lean_Expr_isConstOf(x_1616, x_1693);
lean_dec(x_1616);
if (x_1694 == 0)
{
lean_object* x_1695; 
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1604);
lean_dec(x_1597);
lean_inc(x_3);
lean_inc(x_6);
x_1695 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_6, x_3, x_1617);
if (lean_obj_tag(x_1695) == 0)
{
lean_object* x_1696; 
x_1696 = lean_ctor_get(x_1695, 0);
lean_inc(x_1696);
if (lean_obj_tag(x_1696) == 0)
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
lean_dec(x_1);
x_1697 = lean_ctor_get(x_1695, 1);
lean_inc(x_1697);
lean_dec(x_1695);
x_1698 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1698, 0, x_1606);
x_1699 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1700 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1700, 0, x_1699);
lean_ctor_set(x_1700, 1, x_1698);
x_1701 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__13;
x_1702 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1702, 0, x_1700);
lean_ctor_set(x_1702, 1, x_1701);
x_1703 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1704 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1704, 0, x_1703);
x_1705 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1705, 0, x_1704);
x_1706 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1706, 0, x_1702);
lean_ctor_set(x_1706, 1, x_1705);
x_1707 = l_Lean_Core_getConstInfo___closed__5;
x_1708 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1708, 0, x_1706);
lean_ctor_set(x_1708, 1, x_1707);
x_1709 = lean_box(0);
x_1710 = l_Lean_Meta_throwOther___rarg(x_1708, x_1709, x_3, x_1697);
lean_dec(x_3);
return x_1710;
}
else
{
lean_object* x_1711; lean_object* x_1712; 
lean_dec(x_1606);
lean_dec(x_6);
x_1711 = lean_ctor_get(x_1695, 1);
lean_inc(x_1711);
lean_dec(x_1695);
x_1712 = lean_ctor_get(x_1696, 0);
lean_inc(x_1712);
lean_dec(x_1696);
x_2 = x_1712;
x_4 = x_1711;
goto _start;
}
}
else
{
uint8_t x_1714; 
lean_dec(x_1606);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1714 = !lean_is_exclusive(x_1695);
if (x_1714 == 0)
{
return x_1695;
}
else
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; 
x_1715 = lean_ctor_get(x_1695, 0);
x_1716 = lean_ctor_get(x_1695, 1);
lean_inc(x_1716);
lean_inc(x_1715);
lean_dec(x_1695);
x_1717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1717, 0, x_1715);
lean_ctor_set(x_1717, 1, x_1716);
return x_1717;
}
}
}
else
{
lean_object* x_1718; 
x_1718 = lean_box(0);
x_1618 = x_1718;
goto block_1690;
}
}
else
{
lean_object* x_1719; 
lean_dec(x_1616);
x_1719 = lean_box(0);
x_1618 = x_1719;
goto block_1690;
}
block_1690:
{
lean_object* x_1619; 
lean_dec(x_1618);
x_1619 = l_Lean_ConstantInfo_value_x3f(x_1611);
lean_dec(x_1611);
if (lean_obj_tag(x_1619) == 0)
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; 
lean_dec(x_1613);
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1604);
lean_dec(x_1597);
lean_dec(x_1);
x_1620 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1620, 0, x_1606);
x_1621 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__6;
x_1622 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1622, 0, x_1621);
lean_ctor_set(x_1622, 1, x_1620);
x_1623 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__9;
x_1624 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1624, 0, x_1622);
lean_ctor_set(x_1624, 1, x_1623);
x_1625 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1626 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1626, 0, x_1625);
x_1627 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1627, 0, x_1626);
x_1628 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1628, 0, x_1624);
lean_ctor_set(x_1628, 1, x_1627);
x_1629 = l_Lean_Core_getConstInfo___closed__5;
x_1630 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1630, 0, x_1628);
lean_ctor_set(x_1630, 1, x_1629);
x_1631 = lean_box(0);
x_1632 = l_Lean_Meta_throwOther___rarg(x_1630, x_1631, x_3, x_1617);
lean_dec(x_3);
return x_1632;
}
else
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
lean_dec(x_1606);
lean_dec(x_6);
x_1633 = lean_ctor_get(x_1619, 0);
lean_inc(x_1633);
lean_dec(x_1619);
x_1634 = l_Lean_ParserCompiler_preprocessParserBody___rarg(x_1, x_1633);
lean_inc(x_3);
lean_inc(x_1);
x_1635 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_1634, x_3, x_1617);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1635, 1);
lean_inc(x_1637);
lean_dec(x_1635);
x_1655 = l_Lean_mkAppStx___closed__4;
lean_inc(x_1);
x_1656 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed), 6, 2);
lean_closure_set(x_1656, 0, x_1);
lean_closure_set(x_1656, 1, x_1655);
lean_inc(x_3);
x_1657 = l_Lean_Meta_forallTelescope___rarg(x_1613, x_1656, x_3, x_1637);
if (lean_obj_tag(x_1657) == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; uint8_t x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
x_1658 = lean_ctor_get(x_1657, 0);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1657, 1);
lean_inc(x_1659);
lean_dec(x_1657);
x_1660 = lean_box(0);
lean_inc(x_1609);
x_1661 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1661, 0, x_1609);
lean_ctor_set(x_1661, 1, x_1660);
lean_ctor_set(x_1661, 2, x_1658);
x_1662 = lean_box(0);
x_1663 = 0;
x_1664 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1664, 0, x_1661);
lean_ctor_set(x_1664, 1, x_1636);
lean_ctor_set(x_1664, 2, x_1662);
lean_ctor_set_uint8(x_1664, sizeof(void*)*3, x_1663);
x_1665 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1665, 0, x_1664);
x_1666 = lean_ctor_get(x_1659, 0);
lean_inc(x_1666);
x_1667 = l_Lean_Options_empty;
x_1668 = l_Lean_Environment_addAndCompile(x_1666, x_1667, x_1665);
lean_dec(x_1665);
if (lean_obj_tag(x_1668) == 0)
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; uint8_t x_1677; 
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1604);
lean_dec(x_1597);
lean_dec(x_1);
x_1669 = lean_ctor_get(x_1668, 0);
lean_inc(x_1669);
lean_dec(x_1668);
x_1670 = l_Lean_KernelException_toMessageData(x_1669, x_1667);
x_1671 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1670);
x_1672 = l_Lean_Format_pretty(x_1671, x_1667);
x_1673 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1673, 0, x_1672);
x_1674 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1674, 0, x_1673);
x_1675 = lean_box(0);
x_1676 = l_Lean_Meta_throwOther___rarg(x_1674, x_1675, x_3, x_1659);
lean_dec(x_3);
x_1677 = !lean_is_exclusive(x_1676);
if (x_1677 == 0)
{
return x_1676;
}
else
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; 
x_1678 = lean_ctor_get(x_1676, 0);
x_1679 = lean_ctor_get(x_1676, 1);
lean_inc(x_1679);
lean_inc(x_1678);
lean_dec(x_1676);
x_1680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1680, 0, x_1678);
lean_ctor_set(x_1680, 1, x_1679);
return x_1680;
}
}
else
{
lean_object* x_1681; 
x_1681 = lean_ctor_get(x_1668, 0);
lean_inc(x_1681);
lean_dec(x_1668);
x_1638 = x_1681;
x_1639 = x_1659;
goto block_1654;
}
}
else
{
uint8_t x_1682; 
lean_dec(x_1636);
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1604);
lean_dec(x_1597);
lean_dec(x_3);
lean_dec(x_1);
x_1682 = !lean_is_exclusive(x_1657);
if (x_1682 == 0)
{
return x_1657;
}
else
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
x_1683 = lean_ctor_get(x_1657, 0);
x_1684 = lean_ctor_get(x_1657, 1);
lean_inc(x_1684);
lean_inc(x_1683);
lean_dec(x_1657);
x_1685 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1685, 0, x_1683);
lean_ctor_set(x_1685, 1, x_1684);
return x_1685;
}
}
block_1654:
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
lean_inc(x_1609);
x_1640 = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(x_1607, x_1638, x_1597, x_1609);
x_1641 = l_Lean_Meta_setEnv(x_1640, x_3, x_1639);
x_1642 = lean_ctor_get(x_1641, 1);
lean_inc(x_1642);
lean_dec(x_1641);
x_1643 = lean_box(0);
x_1644 = l_Lean_mkConst(x_1609, x_1643);
lean_inc(x_3);
lean_inc(x_1644);
x_1645 = l_Lean_Meta_inferType(x_1644, x_3, x_1642);
if (lean_obj_tag(x_1645) == 0)
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
x_1646 = lean_ctor_get(x_1645, 0);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1645, 1);
lean_inc(x_1647);
lean_dec(x_1645);
x_1648 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed), 8, 4);
lean_closure_set(x_1648, 0, x_1);
lean_closure_set(x_1648, 1, x_1614);
lean_closure_set(x_1648, 2, x_1604);
lean_closure_set(x_1648, 3, x_1644);
x_1649 = l_Lean_Meta_forallTelescope___rarg(x_1646, x_1648, x_3, x_1647);
return x_1649;
}
else
{
uint8_t x_1650; 
lean_dec(x_1644);
lean_dec(x_1604);
lean_dec(x_3);
lean_dec(x_1);
x_1650 = !lean_is_exclusive(x_1645);
if (x_1650 == 0)
{
return x_1645;
}
else
{
lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; 
x_1651 = lean_ctor_get(x_1645, 0);
x_1652 = lean_ctor_get(x_1645, 1);
lean_inc(x_1652);
lean_inc(x_1651);
lean_dec(x_1645);
x_1653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1653, 0, x_1651);
lean_ctor_set(x_1653, 1, x_1652);
return x_1653;
}
}
}
}
else
{
uint8_t x_1686; 
lean_dec(x_1613);
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1604);
lean_dec(x_1597);
lean_dec(x_3);
lean_dec(x_1);
x_1686 = !lean_is_exclusive(x_1635);
if (x_1686 == 0)
{
return x_1635;
}
else
{
lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1687 = lean_ctor_get(x_1635, 0);
x_1688 = lean_ctor_get(x_1635, 1);
lean_inc(x_1688);
lean_inc(x_1687);
lean_dec(x_1635);
x_1689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1689, 0, x_1687);
lean_ctor_set(x_1689, 1, x_1688);
return x_1689;
}
}
}
}
}
else
{
uint8_t x_1720; 
lean_dec(x_1613);
lean_dec(x_1611);
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1606);
lean_dec(x_1604);
lean_dec(x_1597);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1720 = !lean_is_exclusive(x_1615);
if (x_1720 == 0)
{
return x_1615;
}
else
{
lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; 
x_1721 = lean_ctor_get(x_1615, 0);
x_1722 = lean_ctor_get(x_1615, 1);
lean_inc(x_1722);
lean_inc(x_1721);
lean_dec(x_1615);
x_1723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1723, 0, x_1721);
lean_ctor_set(x_1723, 1, x_1722);
return x_1723;
}
}
}
else
{
uint8_t x_1724; 
lean_dec(x_1609);
lean_dec(x_1607);
lean_dec(x_1606);
lean_dec(x_1604);
lean_dec(x_1597);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1724 = !lean_is_exclusive(x_1610);
if (x_1724 == 0)
{
return x_1610;
}
else
{
lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; 
x_1725 = lean_ctor_get(x_1610, 0);
x_1726 = lean_ctor_get(x_1610, 1);
lean_inc(x_1726);
lean_inc(x_1725);
lean_dec(x_1610);
x_1727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1727, 0, x_1725);
lean_ctor_set(x_1727, 1, x_1726);
return x_1727;
}
}
}
else
{
lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; 
lean_dec(x_1607);
lean_dec(x_1606);
lean_dec(x_1597);
lean_dec(x_6);
x_1728 = lean_ctor_get(x_1608, 0);
lean_inc(x_1728);
lean_dec(x_1608);
x_1729 = lean_box(0);
x_1730 = l_Lean_mkConst(x_1728, x_1729);
lean_inc(x_3);
lean_inc(x_1730);
x_1731 = l_Lean_Meta_inferType(x_1730, x_3, x_1584);
if (lean_obj_tag(x_1731) == 0)
{
lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
x_1732 = lean_ctor_get(x_1731, 0);
lean_inc(x_1732);
x_1733 = lean_ctor_get(x_1731, 1);
lean_inc(x_1733);
lean_dec(x_1731);
x_1734 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed), 7, 3);
lean_closure_set(x_1734, 0, x_1);
lean_closure_set(x_1734, 1, x_1604);
lean_closure_set(x_1734, 2, x_1730);
x_1735 = l_Lean_Meta_forallTelescope___rarg(x_1732, x_1734, x_3, x_1733);
return x_1735;
}
else
{
uint8_t x_1736; 
lean_dec(x_1730);
lean_dec(x_1604);
lean_dec(x_3);
lean_dec(x_1);
x_1736 = !lean_is_exclusive(x_1731);
if (x_1736 == 0)
{
return x_1731;
}
else
{
lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; 
x_1737 = lean_ctor_get(x_1731, 0);
x_1738 = lean_ctor_get(x_1731, 1);
lean_inc(x_1738);
lean_inc(x_1737);
lean_dec(x_1731);
x_1739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1739, 0, x_1737);
lean_ctor_set(x_1739, 1, x_1738);
return x_1739;
}
}
}
}
else
{
lean_object* x_1740; 
lean_dec(x_1585);
lean_dec(x_1);
x_1740 = lean_box(0);
x_1586 = x_1740;
goto block_1596;
}
block_1596:
{
lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
lean_dec(x_1586);
x_1587 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_1588 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1588, 0, x_1587);
x_1589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1589, 0, x_1588);
x_1590 = l_Lean_ParserCompiler_compileParserBody___main___rarg___closed__3;
x_1591 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1591, 0, x_1590);
lean_ctor_set(x_1591, 1, x_1589);
x_1592 = l_Lean_Core_getConstInfo___closed__5;
x_1593 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1593, 0, x_1591);
lean_ctor_set(x_1593, 1, x_1592);
x_1594 = lean_box(0);
x_1595 = l_Lean_Meta_throwOther___rarg(x_1593, x_1594, x_3, x_1584);
lean_dec(x_3);
return x_1595;
}
}
}
}
else
{
uint8_t x_1741; 
lean_dec(x_3);
lean_dec(x_1);
x_1741 = !lean_is_exclusive(x_5);
if (x_1741 == 0)
{
return x_5;
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; 
x_1742 = lean_ctor_get(x_5, 0);
x_1743 = lean_ctor_get(x_5, 1);
lean_inc(x_1743);
lean_inc(x_1742);
lean_dec(x_5);
x_1744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1744, 0, x_1742);
lean_ctor_set(x_1744, 1, x_1743);
return x_1744;
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__12___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__16___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__18___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__19___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__21___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__22___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__24___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__25___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__27___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__28___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__30___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__31___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___at_Lean_ParserCompiler_compileParserBody___main___spec__33___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__18(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__24(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__30(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__33(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParserCompiler_compileParserBody___main___rarg___lambda__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_ParserCompiler_compileParserBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserBody___rarg), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_run___rarg___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_defaultMaxRecDepth;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_ParserCompiler_compileParser___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_Error_Inhabited;
x_2 = lean_alloc_closure((void*)(l_EStateM_Inhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_box(0);
lean_inc(x_3);
x_7 = l_Lean_mkConst(x_3, x_6);
x_8 = l_Lean_MetavarContext_Inhabited___closed__1;
x_9 = l_Lean_Meta_run___rarg___closed__5;
x_10 = l_Lean_NameGenerator_Inhabited___closed__3;
x_11 = l_Lean_TraceState_Inhabited___closed__1;
x_12 = l_Std_PersistentArray_empty___closed__3;
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set(x_13, 5, x_12);
x_14 = l_Lean_ParserCompiler_compileParser___rarg___closed__1;
lean_inc(x_1);
x_15 = l_Lean_ParserCompiler_compileParserBody___main___rarg(x_1, x_7, x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__1(x_19, x_5);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_mk_syntax_ident(x_3);
x_25 = l_Lean_mkOptionalNode___closed__2;
x_26 = lean_array_push(x_25, x_24);
x_27 = l_Lean_nullKind;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
if (x_4 == 0)
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
x_33 = lean_add_attribute(x_23, x_22, x_31, x_28, x_32, x_21);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_38 = lean_add_attribute(x_23, x_22, x_36, x_28, x_37, x_21);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Lean_ParserCompiler_compileParser___rarg___closed__2;
x_41 = l_unreachable_x21___rarg(x_40);
x_42 = lean_apply_1(x_41, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_ctor_get(x_48, 4);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__1(x_50, x_5);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = l_Lean_Meta_Exception_toStr(x_47);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = l_Lean_Meta_Exception_toStr(x_47);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_47);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
return x_51;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
lean_object* l_Lean_ParserCompiler_compileParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParser___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_compileParser___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_interpretParser___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_3);
x_5 = lean_environment_find(x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_2);
x_8 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_ConstantInfo_type(x_14);
lean_dec(x_14);
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
x_20 = lean_eval_const(x_3, x_2);
lean_dec(x_2);
x_21 = l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_20, x_4);
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
x_25 = lean_apply_3(x_24, x_22, x_3, x_23);
return x_25;
}
else
{
uint8_t x_26; 
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
x_31 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_30, x_3, x_2);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_2, x_32, x_4);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_39 = l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_38, x_35);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_34);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
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
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_33, 0);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_33);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
lean_dec(x_31);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_58, x_3, x_2);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; lean_object* x_61; 
x_60 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_61 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_2, x_60, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Lean_Name_append___main(x_2, x_64);
lean_dec(x_2);
x_66 = lean_eval_const(x_62, x_65);
lean_dec(x_65);
x_67 = l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_66, x_63);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_62);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_62);
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
return x_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_59, 0);
lean_inc(x_83);
lean_dec(x_59);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_3);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_4);
return x_85;
}
}
}
}
}
lean_object* l_Lean_ParserCompiler_interpretParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_interpretParser___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_ParserCompiler_interpretParser___spec__3___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
if (x_5 == 0)
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_ParserCompiler_interpretParser___rarg(x_1, x_4, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1), 3, 2);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_10);
x_15 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_13, x_11, x_14);
lean_dec(x_13);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__1), 3, 2);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_18);
x_23 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_21, x_19, x_22);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_ParserCompiler_compileParser___rarg(x_1, x_3, x_4, x_5, x_6);
return x_29;
}
}
}
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed), 6, 1);
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
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_ParserCompiler_registerParserCompiler___rarg___lambda__2(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_2);
return x_8;
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
l_Lean_ParserCompiler_compileParser___rarg___closed__2 = _init_l_Lean_ParserCompiler_compileParser___rarg___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_compileParser___rarg___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
