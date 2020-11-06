// Lean compiler output
// Module: Lean.Elab.BuiltinNotation
// Imports: Init Init.Data.ToString Lean.Compiler.BorrowedAnnotation Lean.Meta.KAbstract Lean.Elab.Term Lean.Elab.Quotation Lean.Elab.SyntheticMVars
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
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__2___closed__3;
lean_object* l_Lean_Elab_Term_expandOrM___closed__2;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__9;
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26;
lean_object* l_Lean_Elab_Term_expandNot___closed__1;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParserMacro(lean_object*);
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
extern lean_object* l_Std_Range___kind_term____x40_Init_Data_Range___hyg_109____closed__12;
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_expandModN___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__2;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Elab_Term_expandBEq(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l_Lean_Elab_Term_expandIf___closed__3;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqRight___closed__2;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__2;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Elab_Term_expandDiv(lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__5;
lean_object* l_Lean_Elab_Term_expandNe(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandModN___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndM(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_expandSeq___closed__3;
lean_object* l_Lean_Elab_Term_expandNot___closed__2;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMap___closed__1;
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__10;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetDeclCore___spec__1___rarg(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_expandPrefixOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandModN___closed__3;
lean_object* l_Lean_Elab_Term_expandShow___closed__12;
lean_object* l_Lean_Elab_Term_expandNot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAndThen___closed__2;
lean_object* l_Lean_Elab_Term_expandHave___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandOr___closed__1;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandIf___closed__5;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Term_expandAssert___closed__10;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandPow(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandModN___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNe___closed__3;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBAnd(lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__17;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1;
lean_object* l_Lean_Elab_Term_expandHEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNe___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_expandModN___closed__4;
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandSubtype___closed__9;
lean_object* l_Lean_Elab_Term_expandBNot(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__44;
lean_object* l_Lean_Elab_Term_elabSubst_match__1___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandMul(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_186____closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__2___closed__13;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandModN(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__8;
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__2___closed__6;
extern lean_object* l_Lean_Init_LeanInit___instance__9;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
extern lean_object* l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNe(lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__1;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_expandSeqRight___closed__3;
lean_object* l_Lean_Elab_Term_expandDiv___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNe___closed__2;
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOrM___closed__1;
lean_object* l_Lean_Elab_Term_expandSeqRight(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_expandGT___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLE___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBOr(lean_object*);
lean_object* l_Lean_Elab_Term_expandPow___closed__2;
lean_object* l_Lean_Elab_Term_elabPanic___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandHEq(lean_object*);
lean_object* l_Lean_Elab_Term_expandPow___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__11;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandModN___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandPow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOrM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandUMinus___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_expandAssert___closed__12;
lean_object* l_Lean_Elab_Term_expandAssert_match__1(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19;
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDollar(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_markBorrowed___closed__1;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_502____closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNot___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__1;
lean_object* l_Lean_Elab_Term_expandUMinus(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__12;
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1;
lean_object* l_Lean_Elab_Term_expandGT___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_502____closed__9;
lean_object* l_Lean_Elab_Term_elabNativeRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__13;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_expandSubtype(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2;
lean_object* l_Lean_Elab_Term_expandLT(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__1;
lean_object* l_Lean_Elab_Term_expandOrM(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandIf___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndM___closed__2;
lean_object* l_Lean_Elab_Term_elabParen___closed__3;
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
extern lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNot___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSubtype___closed__10;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBind___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
extern lean_object* l_Lean_interpolatedStrKind;
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1;
lean_object* l_Lean_Elab_Term_expandHEq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__9;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert___closed__3;
extern lean_object* l_Array_getEvenElems___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___closed__7;
lean_object* l_Lean_Elab_Term_elabPanic___closed__6;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandCons___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_evalNat___closed__8;
lean_object* l_Lean_Elab_Term_expandSeqLeft___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndM___closed__1;
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__11;
lean_object* l_Lean_Elab_Term_expandSubtype___closed__11;
lean_object* l_Lean_Elab_Term_ExpandFComp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandProd___closed__3;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandIf___closed__10;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandModN(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Elab_Term_elabNativeRefl___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandOr___closed__3;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_502____closed__7;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSub(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__5;
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__2;
lean_object* l_Lean_Elab_Term_expandShow___closed__1;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollar___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Elab_Term_expandSorry___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMod___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_object* l___regBuiltin_Lean_Elab_Term_expandPow___closed__2;
lean_object* l_Lean_Elab_Term_expandSubtype___closed__1;
lean_object* l_Lean_Elab_Term_expandAndM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEquiv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAndM___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
lean_object* l_Lean_Elab_Term_expandAssert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMap(lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandMap___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___closed__3;
lean_object* l_Lean_Elab_Term_expandUMinus___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__4;
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandDiv___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAnd(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandMod(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
lean_object* l_Lean_Elab_Term_expandBind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBOr___closed__3;
lean_object* l_Lean_Elab_Term_expandShow___closed__16;
extern lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandOrElse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandInfix(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqLeft(lean_object*);
lean_object* l_Lean_Elab_Term_expandSeq___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTParserMacro(lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_502____closed__3;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__10;
lean_object* l_Lean_Elab_Term_expandShow___closed__2;
lean_object* l_Lean_Elab_Term_expandAndM___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_reduceNat_x3f___closed__12;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__7;
lean_object* l_Lean_Elab_Term_expandAssert_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandGT___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLE(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandBEq___closed__1;
lean_object* l_Lean_Elab_Term_expandInfixOp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeq___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNot(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDiv___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_object* l_Lean_Elab_Term_elabParen___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBind(lean_object*);
lean_object* l_Lean_Elab_Term_expandAndThen___closed__3;
lean_object* l_Lean_Elab_Term_expandUMinus___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSubtype___closed__6;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeq___closed__2;
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandIff___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUMinus___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___closed__10;
lean_object* l_Lean_Elab_Term_elabNativeRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__3;
lean_object* l_Lean_Elab_Term_expandShow___closed__7;
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSub(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6;
lean_object* l_Lean_Elab_Term_expandAssert___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandOr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandGE___closed__2;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAdd___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave___closed__1;
lean_object* l_Lean_Elab_Term_elabNativeDecide(lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__6;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabNativeRefl___closed__1;
lean_object* l_Lean_Elab_Term_expandAppend___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__1;
lean_object* l_Lean_Elab_Term_expandGT(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_evalNat___closed__7;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__11;
lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMod___closed__1;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10;
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDiv___closed__1;
extern lean_object* l_Lean_Meta_mkDecide___rarg___closed__1;
lean_object* l_Lean_Elab_Term_expandPow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBAnd___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandProd(lean_object*);
lean_object* l_Lean_Elab_Term_expandAndM(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandGE___closed__1;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__18;
lean_object* l_Lean_Elab_Term_expandDiv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSub___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Elab_Term_expandBEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__15;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__2;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandBEq___closed__1;
lean_object* l_Lean_Elab_Term_expandMod___closed__1;
lean_object* l_Lean_Elab_Term_expandIf___closed__4;
lean_object* l_Lean_Elab_Term_expandBOr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__2___closed__10;
lean_object* l_Lean_Elab_Term_ExpandFComp___closed__4;
lean_object* l_Lean_Elab_Term_expandBAnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1;
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__6;
lean_object* l_Lean_Elab_Term_elabDecide___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAppend(lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___closed__3;
lean_object* l_Lean_Elab_Term_expandAndThen___closed__1;
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_reduceNat_x3f___closed__10;
extern lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandProd___closed__2;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__3;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_object* l_Lean_Elab_Term_expandAndThen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandIf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandGE___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNe___closed__1;
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
lean_object* l_Lean_Elab_Term_expandPrefixOp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__5;
lean_object* l_Lean_Elab_Term_expandEquiv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__6;
lean_object* l_Lean_Elab_Term_elabTParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_expandIf___closed__6;
lean_object* l_Lean_Elab_Term_expandEq(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDecide(lean_object*);
lean_object* l_Lean_Elab_Term_expandGE___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__5;
lean_object* l_Lean_Elab_Term_expandEquiv___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__14;
lean_object* l_Lean_Elab_Term_expandShow___closed__5;
lean_object* l_Lean_Elab_Term_expandShow___closed__15;
lean_object* l_Lean_Elab_Term_elabSubst_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_expandBEq___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__3;
lean_object* l_Lean_Elab_Term_expandEquiv___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__2;
lean_object* l_Lean_Elab_Term_expandGE___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__1;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLE___closed__2;
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Elab_Term_expandBNot___closed__1;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__8;
lean_object* l_Lean_Elab_Term_expandIf___closed__9;
extern lean_object* l___kind_tactic____x40_Init_Tactics___hyg_461____closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_object*);
lean_object* l_Lean_Elab_Term_expandAndThen___closed__4;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__41;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNe___closed__2;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__7;
lean_object* l_Lean_Elab_Term_expandShow___closed__11;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAdd___closed__1;
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandGT(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAnd___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDollar___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUMinus___closed__4;
lean_object* l_Lean_Elab_Term_expandDollar___closed__1;
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandPow___closed__1;
lean_object* l_Lean_Elab_Term_expandSubtype___closed__8;
lean_object* l_Lean_Elab_Term_elabDecide___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandMul(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__6___lambda__1___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMod___closed__2;
lean_object* l_Lean_Elab_Term_expandBNot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__14;
lean_object* l_Lean_Elab_Term_expandDollar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandProd___closed__1;
lean_object* l_Lean_Elab_Term_expandSubtype___closed__4;
lean_object* l_Lean_Elab_Term_expandAssert___closed__16;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__9;
lean_object* l_Lean_Elab_Term_expandInfixOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_expandEquiv___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__3;
lean_object* l_Lean_Elab_Term_expandProd___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__2;
extern lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLT(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandUMinus(lean_object*);
lean_object* l_Lean_Elab_Term_expandBNe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrM(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__16;
lean_object* l_Lean_Meta_mkArrow___at_Lean_Elab_Term_elabStateRefT___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandBNe___closed__1;
lean_object* l_Lean_Elab_Term_expandMap___closed__3;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__7;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1;
lean_object* l_Lean_Elab_Term_expandProd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst_match__1(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSubtype(lean_object*);
extern lean_object* l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__5;
extern lean_object* l_Lean_Meta_evalNat___closed__14;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBOr___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAnd___closed__3;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2;
lean_object* l_Lean_Elab_Term_expandAssert___closed__13;
lean_object* l_Lean_Elab_Term_expandMod___closed__3;
lean_object* l_Lean_Elab_Term_expandSuffices___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandIf___closed__11;
lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDecide___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabPanic___closed__11;
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Elab_Term_expandDiv___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_502____closed__10;
extern lean_object* l_Lean_setOptionFromString___closed__5;
extern lean_object* l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__2;
extern lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6;
lean_object* l_Lean_Elab_Term_expandPow___closed__4;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4;
extern lean_object* l_Lean_Meta_substCore___lambda__13___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_object*);
lean_object* l_Lean_Elab_Term_expandIff(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAdd(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandBOr___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__7;
lean_object* l_Lean_Elab_Term_ExpandFComp___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandLT___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__1;
lean_object* l_Lean_Elab_Term_elabDecide___boxed(lean_object*);
extern lean_object* l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__4;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__10;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLT___closed__3;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l_Lean_Elab_Term_expandAppend___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNot___closed__2;
extern lean_object* l_Lean_Meta_evalNat___closed__15;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandBAnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSubtype___closed__7;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__6;
lean_object* l_Lean_Elab_Term_expandLE___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___closed__2;
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1;
lean_object* l_Lean_Elab_Term_expandShow___closed__6;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7;
lean_object* l_Lean_Elab_Term_expandBAnd___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2;
extern lean_object* l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__1;
lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandGE(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1;
lean_object* l_Lean_Elab_Term_expandMul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl(lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__10;
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(lean_object*, lean_object*);
extern lean_object* l___kind_tactic____x40_Init_Tactics___hyg_461____closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMapRev(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__3;
lean_object* l_Lean_Elab_Term_ExpandFComp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandNot___closed__1;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandBOr___closed__1;
lean_object* l_Lean_Elab_Term_ExpandFComp___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandIff___closed__3;
lean_object* l_Lean_Elab_Term_expandModN___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_object* l_Lean_Elab_Term_expandSuffices___closed__2;
lean_object* l_Lean_Elab_Term_expandSubtype___closed__3;
lean_object* l_Lean_Elab_Term_expandEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandModN___closed__3;
lean_object* l_Lean_Elab_Term_expandIf___closed__12;
lean_object* l_Lean_Elab_Term_expandHave(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___boxed(lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandOr___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1;
lean_object* l_Lean_Elab_Term_expandLE(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3;
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___closed__13;
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__12;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSubtype___closed__1;
extern lean_object* l_Lean_Elab_macroAttribute;
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Elab_Term_elabParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSubtype___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
lean_object* l_Lean_Elab_Term_expandSorry___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_object* l_Lean_Elab_Term_expandAppend(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__2___closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__42;
lean_object* l___regBuiltin_Lean_Elab_Term_expandDiv(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_expandGE(lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBind___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandIff(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_expandIf___closed__1;
lean_object* l_Lean_Elab_Term_expandMapRev(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_expandOr___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAdd(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__7;
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandCons(lean_object*);
lean_object* l_Lean_Elab_Term_expandMap___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandNot(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandBind(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__8___closed__1;
lean_object* l_Lean_Elab_Term_expandAssert___closed__14;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_338____closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandIff___closed__2;
lean_object* l_Lean_Elab_Term_expandIf___closed__2;
lean_object* l_Lean_Elab_Term_expandOr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOr___closed__1;
lean_object* l_Lean_Elab_Term_expandIf___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__3;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__3;
lean_object* l_Lean_Elab_Term_expandShow___closed__10;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst(lean_object*);
lean_object* l_Lean_Elab_Term_expandOr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
lean_object* l_Lean_Elab_Term_expandBEq___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSorry(lean_object*);
extern lean_object* l___kind_tactic____x40_Init_Tactics___hyg_2____closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__2;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__10;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_elabPanic_match__1(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15;
lean_object* l_Lean_Elab_Term_elabPanic___closed__12;
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Term_expandSubtype___closed__5;
extern lean_object* l_Lean_Name_hasMacroScopes___closed__1;
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDecide(lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__18;
lean_object* l_Lean_Elab_Term_expandShow___closed__8;
lean_object* l_Lean_Syntax_getPos(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12;
lean_object* l_Lean_Elab_Term_expandSeqLeft___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__12;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__8;
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__10;
lean_object* l_Lean_Elab_Term_expandNe___closed__2;
lean_object* l_Lean_Elab_Term_expandShow___closed__9;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17;
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__5;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandEq(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_expandNe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_elabPanic___closed__2;
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqLeft___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrM___closed__1;
lean_object* l_Lean_Elab_Term_expandNe___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__3;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__9;
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollar(lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__11;
extern lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__19;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Data_Repr___instance__2___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandCons___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___closed__4;
lean_object* l_Lean_Elab_Term_ExpandFComp___closed__3;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEq___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrM___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___closed__9;
lean_object* l_Lean_Elab_Term_expandBOr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__9;
extern lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__2;
lean_object* l_Lean_Elab_Term_elabPanic___closed__1;
lean_object* l_Lean_Elab_Term_expandShow___closed__4;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__1;
lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object*, lean_object*);
extern lean_object* l___kind_tactic____x40_Init_Tactics___hyg_2____closed__6;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__3;
lean_object* l_Lean_Elab_Term_expandSubtype___closed__12;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_ExpandFComp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandLT___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSub___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLE___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2;
lean_object* l_Lean_Elab_Term_expandCons___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNot___closed__3;
lean_object* l_Lean_Elab_Term_elabBorrowed___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandGT___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandHEq___closed__3;
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndThen(lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__2;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeDecide___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandIf(lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__9;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMul___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8;
lean_object* l_Lean_Elab_Term_elabPanic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isMonad_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandMul___closed__2;
lean_object* l_Lean_Elab_Term_expandMapRev___closed__1;
lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeq(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_mkPairs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__4;
lean_object* l_Lean_Elab_Term_expandInfix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrElse(lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNot___closed__3;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic___closed__3;
lean_object* l_Lean_Elab_Term_expandSuffices(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_expandBNe(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_expandAssert___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandGT___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__15;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCons(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_expandSeq___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandIf___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___closed__8;
lean_object* l_Lean_Elab_Term_expandMap___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13;
lean_object* l_Lean_Elab_Term_expandMap___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
lean_object* l_Lean_Meta_mkArrow___at_Lean_Elab_Term_elabStateRefT___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandBEq(lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqLeft___closed__4;
lean_object* l_Lean_Elab_Term_expandSeq___closed__4;
extern lean_object* l_Lean_Meta_mkLe___rarg___closed__3;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
lean_object* l_Lean_Elab_Term_expandMapRev___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__9;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandHEq___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandIff___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandAppend___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandNe(lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSub___closed__1;
lean_object* l_Lean_Elab_Term_expandMapRev___closed__2;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
lean_object* l_Lean_Elab_Term_expandMap___closed__4;
lean_object* l_Lean_Elab_Term_tryPostponeIfHasMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEquiv(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandLT___closed__1;
lean_object* l_Lean_Elab_Term_expandAssert___closed__8;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__5;
extern lean_object* l_Lean_levelOne;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
lean_object* l_Lean_Elab_Term_expandMap(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandGE___closed__3;
lean_object* l_Lean_Elab_Term_expandAnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqRight___closed__4;
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_expandAssert___closed__17;
extern lean_object* l_Lean_Meta_mkLt___rarg___closed__3;
uint8_t l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert(lean_object*);
lean_object* l_Lean_Elab_Term_expandAppend___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Elab_Term_expandPow___closed__3;
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAppend___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33;
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAnd___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
lean_object* l_Lean_Elab_Term_expandAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___closed__14;
lean_object* l_Lean_Elab_Term_expandGT___closed__2;
lean_object* l_Lean_Elab_Term_expandAssert___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOrElse(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeq(lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___closed__3;
lean_object* l_Lean_Elab_Term_elabSubst___closed__6;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1;
extern lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__9;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__4;
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__2;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__16;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqRight(lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAnd___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBind___closed__2;
lean_object* l_Lean_Meta_mkAppOptM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqRight___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__4;
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
lean_object* l___regBuiltin_Lean_Elab_Term_expandHEq___closed__1;
lean_object* l_Lean_Elab_Term_expandAssert___closed__2;
lean_object* l_Lean_Elab_Term_expandSeqRight___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSeqLeft___closed__3;
lean_object* l_Lean_Elab_Term_expandAnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandBNe___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1;
lean_object* l_Lean_markBorrowed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNot(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandAndThen(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__4;
lean_object* l_Lean_Elab_Term_expandSeq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__3;
lean_object* l_Lean_Elab_Term_elabSubst___closed__1;
static lean_object* _init_l_Lean_Elab_Term_expandDollar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dollar");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDollar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandDollar___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandDollar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_expandDollar___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_mkAppStx___closed__8;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Array_empty___closed__1;
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_20, x_19);
x_23 = l_Lean_nullKind___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_array_push(x_21, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = l_Lean_Syntax_getArgs(x_15);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = l_Lean_Syntax_getArg(x_1, x_30);
lean_dec(x_1);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_15);
x_35 = lean_array_push(x_33, x_32);
x_36 = l_Lean_nullKind___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_34, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = l_Lean_Syntax_getArg(x_15, x_14);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_getArg(x_15, x_42);
lean_dec(x_15);
x_44 = l_Lean_Syntax_getArg(x_1, x_30);
lean_dec(x_1);
x_45 = l_Lean_Syntax_getArgs(x_43);
lean_dec(x_43);
x_46 = lean_array_push(x_45, x_44);
x_47 = l_Array_empty___closed__1;
x_48 = lean_array_push(x_47, x_41);
x_49 = l_Array_append___rarg(x_47, x_46);
lean_dec(x_46);
x_50 = l_Lean_nullKind___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_48, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandDollar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandDollar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDollar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandDollar___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Elab_Term_expandDollar___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandDollar___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ite");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandIf___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandIf___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandIf___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandIf___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandIf___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandIf___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dite");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandIf___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandIf___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandIf___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandIf___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandIf___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandIf___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandIf___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandIf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(7u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lean_Syntax_getArgs(x_15);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_28 = l_Lean_Syntax_getArg(x_1, x_22);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_31 = lean_unsigned_to_nat(6u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
lean_dec(x_1);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
x_35 = l_Lean_Elab_Term_expandIf___closed__4;
x_36 = l_Lean_addMacroScope(x_34, x_35, x_33);
x_37 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_38 = l_Lean_Elab_Term_expandIf___closed__3;
x_39 = l_Lean_Elab_Term_expandIf___closed__6;
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Array_empty___closed__1;
x_42 = lean_array_push(x_41, x_40);
x_43 = lean_array_push(x_41, x_28);
x_44 = lean_array_push(x_43, x_30);
x_45 = lean_array_push(x_44, x_32);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_push(x_42, x_46);
x_48 = l_Lean_mkAppStx___closed__8;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_21);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_15, x_51);
lean_dec(x_15);
x_53 = l_Lean_Syntax_getArg(x_1, x_22);
x_54 = lean_unsigned_to_nat(4u);
x_55 = l_Lean_Syntax_getArg(x_1, x_54);
x_56 = lean_unsigned_to_nat(6u);
x_57 = l_Lean_Syntax_getArg(x_1, x_56);
lean_dec(x_1);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = l_Lean_Elab_Term_expandIf___closed__10;
x_61 = l_Lean_addMacroScope(x_59, x_60, x_58);
x_62 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_63 = l_Lean_Elab_Term_expandIf___closed__9;
x_64 = l_Lean_Elab_Term_expandIf___closed__12;
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_64);
x_66 = l_Array_empty___closed__1;
x_67 = lean_array_push(x_66, x_65);
x_68 = lean_array_push(x_66, x_53);
x_69 = lean_array_push(x_66, x_52);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_16);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_66, x_70);
x_72 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
x_73 = lean_array_push(x_71, x_72);
lean_inc(x_73);
x_74 = lean_array_push(x_73, x_55);
x_75 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_78 = lean_array_push(x_77, x_76);
x_79 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_66, x_80);
x_82 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_83 = lean_array_push(x_81, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_16);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_86 = lean_array_push(x_85, x_84);
x_87 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_88 = lean_array_push(x_86, x_87);
x_89 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_68, x_90);
x_92 = lean_array_push(x_73, x_57);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_array_push(x_77, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_66, x_95);
x_97 = lean_array_push(x_96, x_82);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_16);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_push(x_85, x_98);
x_100 = lean_array_push(x_99, x_87);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_push(x_91, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_16);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_push(x_67, x_103);
x_105 = l_Lean_mkAppStx___closed__8;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_3);
return x_107;
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandIf), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandIf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandIf___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subtype");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandSubtype___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Subtype");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandSubtype___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandSubtype___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandSubtype___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSubtype___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSubtype___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSubtype___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_2 = l_myMacro____x40_Init_Tactics___hyg_502____closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_2 = l_Lean_Elab_Term_expandSubtype___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandSubtype___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSubtype___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Term_expandSubtype___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSubtype(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_expandSubtype___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_nullKind___closed__2;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Syntax_getArgs(x_17);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_23, x_14);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
lean_dec(x_1);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_Elab_Term_expandSubtype___closed__6;
x_34 = l_Lean_addMacroScope(x_32, x_33, x_31);
x_35 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_36 = l_Lean_Elab_Term_expandSubtype___closed__5;
x_37 = l_Lean_Elab_Term_expandSubtype___closed__8;
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Array_empty___closed__1;
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_array_push(x_39, x_15);
x_42 = l_Lean_Elab_Term_expandSubtype___closed__12;
x_43 = lean_array_push(x_41, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_46 = lean_array_push(x_45, x_44);
x_47 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_48 = lean_array_push(x_46, x_47);
x_49 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_array_push(x_39, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_39, x_52);
x_54 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_30);
x_57 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_60 = lean_array_push(x_59, x_58);
x_61 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_array_push(x_39, x_62);
x_64 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_65 = lean_array_push(x_63, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_18);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_45, x_66);
x_68 = lean_array_push(x_67, x_47);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_39, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_18);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_40, x_71);
x_73 = l_Lean_mkAppStx___closed__8;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_23);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Syntax_getArg(x_17, x_76);
lean_dec(x_17);
x_78 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_inc(x_77);
x_79 = l_Lean_Syntax_isOfKind(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(1);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_3);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = l_Lean_Syntax_getArgs(x_77);
x_83 = lean_array_get_size(x_82);
lean_dec(x_82);
x_84 = lean_nat_dec_eq(x_83, x_16);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(1);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_87 = l_Lean_Syntax_getArg(x_77, x_14);
lean_dec(x_77);
x_88 = lean_unsigned_to_nat(4u);
x_89 = l_Lean_Syntax_getArg(x_1, x_88);
lean_dec(x_1);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
lean_dec(x_2);
x_92 = l_Lean_Elab_Term_expandSubtype___closed__6;
x_93 = l_Lean_addMacroScope(x_91, x_92, x_90);
x_94 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_95 = l_Lean_Elab_Term_expandSubtype___closed__5;
x_96 = l_Lean_Elab_Term_expandSubtype___closed__8;
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_96);
x_98 = l_Array_empty___closed__1;
x_99 = lean_array_push(x_98, x_97);
x_100 = lean_array_push(x_98, x_15);
x_101 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_102 = lean_array_push(x_101, x_87);
x_103 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_array_push(x_98, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_18);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_100, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_18);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_110 = lean_array_push(x_109, x_108);
x_111 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_112 = lean_array_push(x_110, x_111);
x_113 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_array_push(x_98, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_18);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_array_push(x_98, x_116);
x_118 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
x_119 = lean_array_push(x_117, x_118);
x_120 = lean_array_push(x_119, x_89);
x_121 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_124 = lean_array_push(x_123, x_122);
x_125 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_array_push(x_98, x_126);
x_128 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_129 = lean_array_push(x_127, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_18);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_push(x_109, x_130);
x_132 = lean_array_push(x_131, x_111);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_113);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_push(x_98, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_18);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_99, x_135);
x_137 = l_Lean_mkAppStx___closed__8;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_3);
return x_139;
}
}
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSubtype___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSubtype), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSubtype(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Elab_Term_expandSubtype___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSubtype___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymousCtor");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_elabAnonymousCtor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be known");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be an inductive type ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Term_elabAnonymousCtor___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Syntax_getArgs(x_1);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn(x_28);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_60; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_8, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_60 = lean_environment_find(x_35, x_31);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_61 = l_Lean_indentExpr(x_28);
x_62 = l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
lean_dec(x_60);
if (lean_obj_tag(x_67) == 5)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_ctor_get(x_68, 4);
lean_inc(x_69);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_70 = l_Lean_indentExpr(x_28);
x_71 = l_Lean_Elab_Term_elabAnonymousCtor___closed__9;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_28);
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
x_78 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_34);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_mkCIdentFrom(x_1, x_77);
x_83 = l_Array_empty___closed__1;
x_84 = lean_array_push(x_83, x_82);
x_85 = lean_array_get_size(x_20);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_lt(x_86, x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_85);
lean_dec(x_20);
x_88 = l_Lean_Elab_Term_elabAnonymousCtor___closed__11;
x_89 = lean_array_push(x_84, x_88);
x_90 = l_Lean_mkAppStx___closed__8;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_36 = x_91;
x_37 = x_81;
goto block_59;
}
else
{
uint8_t x_92; 
x_92 = lean_nat_dec_le(x_85, x_85);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_85);
lean_dec(x_20);
x_93 = l_Lean_Elab_Term_elabAnonymousCtor___closed__11;
x_94 = lean_array_push(x_84, x_93);
x_95 = l_Lean_mkAppStx___closed__8;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_36 = x_96;
x_37 = x_81;
goto block_59;
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_97 = 0;
x_98 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_99 = l_Array_getEvenElems___rarg___closed__1;
x_100 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_getSepArgs___spec__1(x_20, x_97, x_98, x_99);
lean_dec(x_20);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Array_append___rarg(x_83, x_101);
lean_dec(x_101);
x_103 = l_Lean_nullKind___closed__2;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_array_push(x_84, x_104);
x_106 = l_Lean_mkAppStx___closed__8;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_36 = x_107;
x_37 = x_81;
goto block_59;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_76);
lean_dec(x_69);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_108 = l_Lean_indentExpr(x_28);
x_109 = l_Lean_Elab_Term_elabAnonymousCtor___closed__9;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_67);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_114 = l_Lean_indentExpr(x_28);
x_115 = l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_118, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_119;
}
}
block_59:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_3, 6);
lean_inc(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_3, 6, x_41);
x_42 = 1;
x_43 = l_Lean_Elab_Term_elabTerm(x_36, x_2, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
x_48 = lean_ctor_get(x_3, 4);
x_49 = lean_ctor_get(x_3, 5);
x_50 = lean_ctor_get(x_3, 6);
x_51 = lean_ctor_get(x_3, 7);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
lean_inc(x_36);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_49);
lean_ctor_set(x_56, 6, x_55);
lean_ctor_set(x_56, 7, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*8, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 1, x_53);
x_57 = 1;
x_58 = l_Lean_Elab_Term_elabTerm(x_36, x_2, x_57, x_56, x_4, x_5, x_6, x_7, x_8, x_37);
return x_58;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_120 = l_Lean_indentExpr(x_28);
x_121 = l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_27);
if (x_126 == 0)
{
return x_27;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_27, 0);
x_128 = lean_ctor_get(x_27, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_27);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_21);
if (x_130 == 0)
{
return x_21;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_21, 0);
x_132 = lean_ctor_get(x_21, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_21);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabBorrowed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_markBorrowed___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabBorrowed___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Syntax_getArgs(x_1);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = 1;
x_21 = l_Lean_Elab_Term_elabTerm(x_19, x_2, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_markBorrowed(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_markBorrowed(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBorrowed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabBorrowed___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("show");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandShow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fromTerm");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandShow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("from");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__10;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("this");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandShow___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandShow___closed__15;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandShow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; uint8_t x_47; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_46 = l_Lean_Elab_Term_expandShow___closed__4;
lean_inc(x_17);
x_47 = l_Lean_Syntax_isOfKind(x_17, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_box(0);
x_18 = x_48;
goto block_45;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Lean_Syntax_getArgs(x_17);
x_50 = lean_array_get_size(x_49);
lean_dec(x_49);
x_51 = lean_nat_dec_eq(x_50, x_16);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = lean_box(0);
x_18 = x_52;
goto block_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_53 = l_Lean_Syntax_getArg(x_17, x_14);
lean_dec(x_17);
x_54 = l_Lean_Elab_Term_expandShow___closed__14;
x_55 = l_Lean_mkIdentFrom(x_1, x_54);
lean_dec(x_1);
x_56 = l_Array_empty___closed__1;
lean_inc(x_55);
x_57 = lean_array_push(x_56, x_55);
x_58 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_59 = lean_array_push(x_57, x_58);
x_60 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_61 = lean_array_push(x_60, x_15);
x_62 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_56, x_63);
x_65 = l_Lean_nullKind___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_array_push(x_59, x_66);
x_68 = l_myMacro____x40_Init_Tactics___hyg_502____closed__10;
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_array_push(x_69, x_53);
x_71 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__8;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_56, x_72);
x_74 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__6;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_Term_expandShow___closed__16;
x_77 = lean_array_push(x_76, x_75);
x_78 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_79 = lean_array_push(x_77, x_78);
x_80 = lean_array_push(x_79, x_55);
x_81 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
return x_83;
}
}
block_45:
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_18);
x_19 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_inc(x_17);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Syntax_getArgs(x_17);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_eq(x_24, x_16);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_15);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Syntax_getArg(x_17, x_14);
lean_dec(x_17);
x_29 = l_myMacro____x40_Init_Tactics___hyg_720____closed__7;
lean_inc(x_28);
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_15);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = l_Lean_Elab_Term_expandShow___closed__6;
x_34 = lean_array_push(x_33, x_15);
x_35 = l_Lean_Elab_Term_expandShow___closed__12;
x_36 = lean_array_push(x_35, x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Term_expandShow___closed__9;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_Elab_Term_expandShow___closed__4;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_array_push(x_34, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandShow(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandShow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandShow___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Elab_Term_expandShow___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandShow___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandHave___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___kind_tactic____x40_Init_Tactics___hyg_461____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandHave___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Tactics___hyg_502____closed__3;
x_2 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandHave(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_myMacro____x40_Init_Tactics___hyg_720____closed__11;
x_5 = l_Lean_mkAtomFrom(x_1, x_4);
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = l_Lean_nullKind;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Syntax_setArg(x_1, x_10, x_9);
x_12 = l_Lean_Elab_Term_expandHave___closed__1;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = l_Lean_Syntax_getArgs(x_11);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(6u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_183; uint8_t x_184; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_11, x_22);
x_183 = l_Lean_nullKind___closed__2;
lean_inc(x_23);
x_184 = l_Lean_Syntax_isOfKind(x_23, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_box(0);
x_24 = x_185;
goto block_182;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = l_Lean_Syntax_getArgs(x_23);
x_187 = lean_array_get_size(x_186);
lean_dec(x_186);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_eq(x_187, x_188);
lean_dec(x_187);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_24 = x_190;
goto block_182;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_247; lean_object* x_287; uint8_t x_288; 
lean_dec(x_23);
x_191 = lean_unsigned_to_nat(2u);
x_192 = l_Lean_Syntax_getArg(x_11, x_191);
x_193 = lean_unsigned_to_nat(3u);
x_194 = l_Lean_Syntax_getArg(x_11, x_193);
x_287 = l_Lean_Elab_Term_expandShow___closed__4;
lean_inc(x_194);
x_288 = l_Lean_Syntax_isOfKind(x_194, x_287);
if (x_288 == 0)
{
lean_object* x_289; 
x_289 = lean_box(0);
x_247 = x_289;
goto block_286;
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = l_Lean_Syntax_getArgs(x_194);
x_291 = lean_array_get_size(x_290);
lean_dec(x_290);
x_292 = lean_nat_dec_eq(x_291, x_191);
lean_dec(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_box(0);
x_247 = x_293;
goto block_286;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = l_Lean_Syntax_getArg(x_194, x_22);
lean_dec(x_194);
x_295 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_295);
x_296 = l_Lean_Syntax_isOfKind(x_295, x_183);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_192);
lean_dec(x_11);
x_297 = lean_box(1);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_3);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = l_Lean_Syntax_getArgs(x_295);
lean_dec(x_295);
x_300 = lean_array_get_size(x_299);
lean_dec(x_299);
x_301 = lean_nat_dec_eq(x_300, x_22);
lean_dec(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_294);
lean_dec(x_192);
lean_dec(x_11);
x_302 = lean_box(1);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_3);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_304 = lean_unsigned_to_nat(5u);
x_305 = l_Lean_Syntax_getArg(x_11, x_304);
x_306 = l_Lean_Elab_Term_expandShow___closed__14;
x_307 = l_Lean_mkIdentFrom(x_11, x_306);
lean_dec(x_11);
x_308 = l_Array_empty___closed__1;
x_309 = lean_array_push(x_308, x_307);
x_310 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_311 = lean_array_push(x_309, x_310);
x_312 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_313 = lean_array_push(x_312, x_192);
x_314 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = lean_array_push(x_308, x_315);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_183);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_array_push(x_311, x_317);
x_319 = l_myMacro____x40_Init_Tactics___hyg_502____closed__10;
x_320 = lean_array_push(x_318, x_319);
x_321 = lean_array_push(x_320, x_294);
x_322 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__8;
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
x_324 = lean_array_push(x_308, x_323);
x_325 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__6;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = l_Lean_Elab_Term_expandShow___closed__16;
x_328 = lean_array_push(x_327, x_326);
x_329 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_330 = lean_array_push(x_328, x_329);
x_331 = lean_array_push(x_330, x_305);
x_332 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_3);
return x_334;
}
}
}
}
block_246:
{
lean_object* x_196; uint8_t x_197; 
lean_dec(x_195);
x_196 = l_myMacro____x40_Init_Tactics___hyg_502____closed__9;
lean_inc(x_194);
x_197 = l_Lean_Syntax_isOfKind(x_194, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_11);
x_198 = lean_box(1);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_3);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = l_Lean_Syntax_getArgs(x_194);
x_201 = lean_array_get_size(x_200);
lean_dec(x_200);
x_202 = lean_nat_dec_eq(x_201, x_191);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_11);
x_203 = lean_box(1);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_3);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = l_Lean_Syntax_getArg(x_194, x_22);
lean_dec(x_194);
x_206 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_206);
x_207 = l_Lean_Syntax_isOfKind(x_206, x_183);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_192);
lean_dec(x_11);
x_208 = lean_box(1);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_3);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = l_Lean_Syntax_getArgs(x_206);
lean_dec(x_206);
x_211 = lean_array_get_size(x_210);
lean_dec(x_210);
x_212 = lean_nat_dec_eq(x_211, x_22);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_205);
lean_dec(x_192);
lean_dec(x_11);
x_213 = lean_box(1);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_3);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_215 = lean_unsigned_to_nat(5u);
x_216 = l_Lean_Syntax_getArg(x_11, x_215);
x_217 = l_Lean_Elab_Term_expandShow___closed__14;
x_218 = l_Lean_mkIdentFrom(x_11, x_217);
lean_dec(x_11);
x_219 = l_Array_empty___closed__1;
x_220 = lean_array_push(x_219, x_218);
x_221 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_222 = lean_array_push(x_220, x_221);
x_223 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_224 = lean_array_push(x_223, x_192);
x_225 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = lean_array_push(x_219, x_226);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_183);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_array_push(x_222, x_228);
x_230 = l_myMacro____x40_Init_Tactics___hyg_502____closed__10;
x_231 = lean_array_push(x_229, x_230);
x_232 = lean_array_push(x_231, x_205);
x_233 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__8;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = lean_array_push(x_219, x_234);
x_236 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__6;
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = l_Lean_Elab_Term_expandShow___closed__16;
x_239 = lean_array_push(x_238, x_237);
x_240 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_241 = lean_array_push(x_239, x_240);
x_242 = lean_array_push(x_241, x_216);
x_243 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_3);
return x_245;
}
}
}
}
}
block_286:
{
lean_object* x_248; uint8_t x_249; 
lean_dec(x_247);
x_248 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_inc(x_194);
x_249 = l_Lean_Syntax_isOfKind(x_194, x_248);
if (x_249 == 0)
{
lean_object* x_250; 
x_250 = lean_box(0);
x_195 = x_250;
goto block_246;
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = l_Lean_Syntax_getArgs(x_194);
x_252 = lean_array_get_size(x_251);
lean_dec(x_251);
x_253 = lean_nat_dec_eq(x_252, x_191);
lean_dec(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = lean_box(0);
x_195 = x_254;
goto block_246;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = l_Lean_Syntax_getArg(x_194, x_22);
lean_dec(x_194);
x_256 = l_myMacro____x40_Init_Tactics___hyg_720____closed__7;
lean_inc(x_255);
x_257 = l_Lean_Syntax_isOfKind(x_255, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_255);
lean_dec(x_192);
lean_dec(x_11);
x_258 = lean_box(1);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_3);
return x_259;
}
else
{
lean_object* x_260; uint8_t x_261; 
x_260 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_260);
x_261 = l_Lean_Syntax_isOfKind(x_260, x_183);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_192);
lean_dec(x_11);
x_262 = lean_box(1);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_3);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_264 = l_Lean_Syntax_getArgs(x_260);
lean_dec(x_260);
x_265 = lean_array_get_size(x_264);
lean_dec(x_264);
x_266 = lean_nat_dec_eq(x_265, x_22);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_255);
lean_dec(x_192);
lean_dec(x_11);
x_267 = lean_box(1);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_3);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_269 = lean_unsigned_to_nat(5u);
x_270 = l_Lean_Syntax_getArg(x_11, x_269);
lean_dec(x_11);
x_271 = l_Lean_Elab_Term_expandHave___closed__2;
x_272 = lean_array_push(x_271, x_192);
x_273 = l_Lean_Elab_Term_expandShow___closed__12;
x_274 = lean_array_push(x_273, x_255);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_248);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_Elab_Term_expandShow___closed__9;
x_277 = lean_array_push(x_276, x_275);
x_278 = l_Lean_Elab_Term_expandShow___closed__4;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = lean_array_push(x_272, x_279);
x_281 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_282 = lean_array_push(x_280, x_281);
x_283 = lean_array_push(x_282, x_270);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_12);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_3);
return x_285;
}
}
}
}
}
}
}
}
block_182:
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_24);
x_25 = l_Lean_nullKind___closed__2;
lean_inc(x_23);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_11);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Syntax_getArgs(x_23);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_11);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; lean_object* x_136; uint8_t x_137; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Syntax_getArg(x_23, x_35);
lean_dec(x_23);
x_37 = l_Lean_Syntax_getArg(x_11, x_31);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_11, x_38);
x_136 = l_Lean_Elab_Term_expandShow___closed__4;
lean_inc(x_39);
x_137 = l_Lean_Syntax_isOfKind(x_39, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_box(0);
x_90 = x_138;
goto block_135;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = l_Lean_Syntax_getArgs(x_39);
x_140 = lean_array_get_size(x_139);
lean_dec(x_139);
x_141 = lean_nat_dec_eq(x_140, x_31);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_box(0);
x_90 = x_142;
goto block_135;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = l_Lean_Syntax_getArg(x_39, x_22);
lean_dec(x_39);
x_144 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_144);
x_145 = l_Lean_Syntax_isOfKind(x_144, x_25);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_146 = lean_box(1);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_3);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = l_Lean_Syntax_getArgs(x_144);
lean_dec(x_144);
x_149 = lean_array_get_size(x_148);
lean_dec(x_148);
x_150 = lean_nat_dec_eq(x_149, x_22);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_151 = lean_box(1);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_3);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_153 = lean_unsigned_to_nat(5u);
x_154 = l_Lean_Syntax_getArg(x_11, x_153);
lean_dec(x_11);
x_155 = l_Array_empty___closed__1;
x_156 = lean_array_push(x_155, x_36);
x_157 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_158 = lean_array_push(x_156, x_157);
x_159 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_160 = lean_array_push(x_159, x_37);
x_161 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_array_push(x_155, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_25);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_158, x_164);
x_166 = l_myMacro____x40_Init_Tactics___hyg_502____closed__10;
x_167 = lean_array_push(x_165, x_166);
x_168 = lean_array_push(x_167, x_143);
x_169 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__8;
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = lean_array_push(x_155, x_170);
x_172 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__6;
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = l_Lean_Elab_Term_expandShow___closed__16;
x_175 = lean_array_push(x_174, x_173);
x_176 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_177 = lean_array_push(x_175, x_176);
x_178 = lean_array_push(x_177, x_154);
x_179 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_3);
return x_181;
}
}
}
}
block_89:
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_40);
x_41 = l_myMacro____x40_Init_Tactics___hyg_502____closed__9;
lean_inc(x_39);
x_42 = l_Lean_Syntax_isOfKind(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Syntax_getArgs(x_39);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = lean_nat_dec_eq(x_46, x_31);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_48 = lean_box(1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Syntax_getArg(x_39, x_22);
lean_dec(x_39);
x_51 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_51);
x_52 = l_Lean_Syntax_isOfKind(x_51, x_25);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lean_Syntax_getArgs(x_51);
lean_dec(x_51);
x_56 = lean_array_get_size(x_55);
lean_dec(x_55);
x_57 = lean_nat_dec_eq(x_56, x_22);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_60 = lean_unsigned_to_nat(5u);
x_61 = l_Lean_Syntax_getArg(x_11, x_60);
lean_dec(x_11);
x_62 = l_Array_empty___closed__1;
x_63 = lean_array_push(x_62, x_36);
x_64 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_65 = lean_array_push(x_63, x_64);
x_66 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__4;
x_67 = lean_array_push(x_66, x_37);
x_68 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_array_push(x_62, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_65, x_71);
x_73 = l_myMacro____x40_Init_Tactics___hyg_502____closed__10;
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_array_push(x_74, x_50);
x_76 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__8;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_62, x_77);
x_79 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__6;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_Term_expandShow___closed__16;
x_82 = lean_array_push(x_81, x_80);
x_83 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_84 = lean_array_push(x_82, x_83);
x_85 = lean_array_push(x_84, x_61);
x_86 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_3);
return x_88;
}
}
}
}
}
block_135:
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_90);
x_91 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_inc(x_39);
x_92 = l_Lean_Syntax_isOfKind(x_39, x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_40 = x_93;
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = l_Lean_Syntax_getArgs(x_39);
x_95 = lean_array_get_size(x_94);
lean_dec(x_94);
x_96 = lean_nat_dec_eq(x_95, x_31);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_box(0);
x_40 = x_97;
goto block_89;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Lean_Syntax_getArg(x_39, x_22);
lean_dec(x_39);
x_99 = l_myMacro____x40_Init_Tactics___hyg_720____closed__7;
lean_inc(x_98);
x_100 = l_Lean_Syntax_isOfKind(x_98, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_101 = lean_box(1);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_3);
return x_102;
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_103);
x_104 = l_Lean_Syntax_isOfKind(x_103, x_25);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_3);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = l_Lean_Syntax_getArgs(x_103);
lean_dec(x_103);
x_108 = lean_array_get_size(x_107);
lean_dec(x_107);
x_109 = lean_nat_dec_eq(x_108, x_22);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_98);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_110 = lean_box(1);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_3);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_112 = lean_unsigned_to_nat(5u);
x_113 = l_Lean_Syntax_getArg(x_11, x_112);
lean_dec(x_11);
x_114 = l_Array_empty___closed__1;
x_115 = lean_array_push(x_114, x_36);
x_116 = l_myMacro____x40_Init_Tactics___hyg_502____closed__4;
x_117 = lean_array_push(x_115, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_25);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_myMacro____x40_Init_Tactics___hyg_502____closed__3;
x_120 = lean_array_push(x_119, x_118);
x_121 = lean_array_push(x_120, x_37);
x_122 = l_Lean_Elab_Term_expandShow___closed__12;
x_123 = lean_array_push(x_122, x_98);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_91);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Elab_Term_expandShow___closed__9;
x_126 = lean_array_push(x_125, x_124);
x_127 = l_Lean_Elab_Term_expandShow___closed__4;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_array_push(x_121, x_128);
x_130 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_131 = lean_array_push(x_129, x_130);
x_132 = lean_array_push(x_131, x_113);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_12);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_3);
return x_134;
}
}
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandHave(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandHave___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Elab_Term_expandHave___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandHave___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSuffices___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("suffices");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSuffices___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandSuffices___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_myMacro____x40_Init_Tactics___hyg_720____closed__11;
x_5 = l_Lean_mkAtomFrom(x_1, x_4);
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = l_Lean_nullKind;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Syntax_setArg(x_1, x_10, x_9);
x_12 = l_Lean_Elab_Term_expandSuffices___closed__2;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = l_Lean_Syntax_getArgs(x_11);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(6u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_127; uint8_t x_128; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_11, x_22);
x_127 = l_Lean_nullKind___closed__2;
lean_inc(x_23);
x_128 = l_Lean_Syntax_isOfKind(x_23, x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_box(0);
x_24 = x_129;
goto block_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = l_Lean_Syntax_getArgs(x_23);
x_131 = lean_array_get_size(x_130);
lean_dec(x_130);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_nat_dec_eq(x_131, x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_24 = x_134;
goto block_126;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_182; uint8_t x_183; 
lean_dec(x_23);
x_135 = lean_unsigned_to_nat(2u);
x_136 = l_Lean_Syntax_getArg(x_11, x_135);
x_137 = lean_unsigned_to_nat(3u);
x_138 = l_Lean_Syntax_getArg(x_11, x_137);
x_182 = l_Lean_Elab_Term_expandShow___closed__4;
lean_inc(x_138);
x_183 = l_Lean_Syntax_isOfKind(x_138, x_182);
if (x_183 == 0)
{
lean_object* x_184; 
x_184 = lean_box(0);
x_139 = x_184;
goto block_181;
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = l_Lean_Syntax_getArgs(x_138);
x_186 = lean_array_get_size(x_185);
lean_dec(x_185);
x_187 = lean_nat_dec_eq(x_186, x_135);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_box(0);
x_139 = x_188;
goto block_181;
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = l_Lean_Syntax_getArg(x_138, x_22);
lean_dec(x_138);
x_190 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_190);
x_191 = l_Lean_Syntax_isOfKind(x_190, x_127);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_136);
lean_dec(x_11);
x_192 = lean_box(1);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_3);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = l_Lean_Syntax_getArgs(x_190);
lean_dec(x_190);
x_195 = lean_array_get_size(x_194);
lean_dec(x_194);
x_196 = lean_nat_dec_eq(x_195, x_22);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_189);
lean_dec(x_136);
lean_dec(x_11);
x_197 = lean_box(1);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_3);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_199 = lean_unsigned_to_nat(5u);
x_200 = l_Lean_Syntax_getArg(x_11, x_199);
lean_dec(x_11);
x_201 = l_Lean_Elab_Term_expandHave___closed__2;
x_202 = lean_array_push(x_201, x_136);
x_203 = l_Lean_Elab_Term_expandShow___closed__9;
x_204 = lean_array_push(x_203, x_200);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_182);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_array_push(x_202, x_205);
x_207 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_208 = lean_array_push(x_206, x_207);
x_209 = lean_array_push(x_208, x_189);
x_210 = l_Lean_Elab_Term_expandHave___closed__1;
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_3);
return x_212;
}
}
}
}
block_181:
{
lean_object* x_140; uint8_t x_141; 
lean_dec(x_139);
x_140 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_inc(x_138);
x_141 = l_Lean_Syntax_isOfKind(x_138, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_11);
x_142 = lean_box(1);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = l_Lean_Syntax_getArgs(x_138);
x_145 = lean_array_get_size(x_144);
lean_dec(x_144);
x_146 = lean_nat_dec_eq(x_145, x_135);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_11);
x_147 = lean_box(1);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_3);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = l_Lean_Syntax_getArg(x_138, x_22);
lean_dec(x_138);
x_150 = l_myMacro____x40_Init_Tactics___hyg_720____closed__7;
lean_inc(x_149);
x_151 = l_Lean_Syntax_isOfKind(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_149);
lean_dec(x_136);
lean_dec(x_11);
x_152 = lean_box(1);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_3);
return x_153;
}
else
{
lean_object* x_154; uint8_t x_155; 
x_154 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_154);
x_155 = l_Lean_Syntax_isOfKind(x_154, x_127);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_136);
lean_dec(x_11);
x_156 = lean_box(1);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_3);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = l_Lean_Syntax_getArgs(x_154);
lean_dec(x_154);
x_159 = lean_array_get_size(x_158);
lean_dec(x_158);
x_160 = lean_nat_dec_eq(x_159, x_22);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_149);
lean_dec(x_136);
lean_dec(x_11);
x_161 = lean_box(1);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_3);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_163 = lean_unsigned_to_nat(5u);
x_164 = l_Lean_Syntax_getArg(x_11, x_163);
lean_dec(x_11);
x_165 = l_Lean_Elab_Term_expandHave___closed__2;
x_166 = lean_array_push(x_165, x_136);
x_167 = l_Lean_Elab_Term_expandShow___closed__9;
x_168 = lean_array_push(x_167, x_164);
x_169 = l_Lean_Elab_Term_expandShow___closed__4;
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = lean_array_push(x_166, x_170);
x_172 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_173 = lean_array_push(x_171, x_172);
x_174 = l_Lean_Elab_Term_expandShow___closed__12;
x_175 = lean_array_push(x_174, x_149);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_140);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_array_push(x_173, x_176);
x_178 = l_Lean_Elab_Term_expandHave___closed__1;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_3);
return x_180;
}
}
}
}
}
}
}
}
block_126:
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_24);
x_25 = l_Lean_nullKind___closed__2;
lean_inc(x_23);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_11);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Syntax_getArgs(x_23);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_11);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_89; uint8_t x_90; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Syntax_getArg(x_23, x_35);
lean_dec(x_23);
x_37 = l_Lean_Syntax_getArg(x_11, x_31);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_11, x_38);
x_89 = l_Lean_Elab_Term_expandShow___closed__4;
lean_inc(x_39);
x_90 = l_Lean_Syntax_isOfKind(x_39, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
x_40 = x_91;
goto block_88;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = l_Lean_Syntax_getArgs(x_39);
x_93 = lean_array_get_size(x_92);
lean_dec(x_92);
x_94 = lean_nat_dec_eq(x_93, x_31);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_40 = x_95;
goto block_88;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = l_Lean_Syntax_getArg(x_39, x_22);
lean_dec(x_39);
x_97 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_97);
x_98 = l_Lean_Syntax_isOfKind(x_97, x_25);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_99 = lean_box(1);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_3);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_Syntax_getArgs(x_97);
lean_dec(x_97);
x_102 = lean_array_get_size(x_101);
lean_dec(x_101);
x_103 = lean_nat_dec_eq(x_102, x_22);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_96);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_104 = lean_box(1);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_3);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_106 = lean_unsigned_to_nat(5u);
x_107 = l_Lean_Syntax_getArg(x_11, x_106);
lean_dec(x_11);
x_108 = l_Array_empty___closed__1;
x_109 = lean_array_push(x_108, x_36);
x_110 = l_myMacro____x40_Init_Tactics___hyg_502____closed__4;
x_111 = lean_array_push(x_109, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_25);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_myMacro____x40_Init_Tactics___hyg_502____closed__3;
x_114 = lean_array_push(x_113, x_112);
x_115 = lean_array_push(x_114, x_37);
x_116 = l_Lean_Elab_Term_expandShow___closed__9;
x_117 = lean_array_push(x_116, x_107);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_89);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_push(x_115, x_118);
x_120 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_121 = lean_array_push(x_119, x_120);
x_122 = lean_array_push(x_121, x_96);
x_123 = l_Lean_Elab_Term_expandHave___closed__1;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_3);
return x_125;
}
}
}
}
block_88:
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_40);
x_41 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_inc(x_39);
x_42 = l_Lean_Syntax_isOfKind(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Syntax_getArgs(x_39);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = lean_nat_dec_eq(x_46, x_31);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_48 = lean_box(1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Syntax_getArg(x_39, x_22);
lean_dec(x_39);
x_51 = l_myMacro____x40_Init_Tactics___hyg_720____closed__7;
lean_inc(x_50);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Syntax_getArg(x_11, x_10);
lean_inc(x_55);
x_56 = l_Lean_Syntax_isOfKind(x_55, x_25);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_57 = lean_box(1);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Syntax_getArgs(x_55);
lean_dec(x_55);
x_60 = lean_array_get_size(x_59);
lean_dec(x_59);
x_61 = lean_nat_dec_eq(x_60, x_22);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
x_62 = lean_box(1);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_64 = lean_unsigned_to_nat(5u);
x_65 = l_Lean_Syntax_getArg(x_11, x_64);
lean_dec(x_11);
x_66 = l_Array_empty___closed__1;
x_67 = lean_array_push(x_66, x_36);
x_68 = l_myMacro____x40_Init_Tactics___hyg_502____closed__4;
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_25);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_myMacro____x40_Init_Tactics___hyg_502____closed__3;
x_72 = lean_array_push(x_71, x_70);
x_73 = lean_array_push(x_72, x_37);
x_74 = l_Lean_Elab_Term_expandShow___closed__9;
x_75 = lean_array_push(x_74, x_65);
x_76 = l_Lean_Elab_Term_expandShow___closed__4;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_73, x_77);
x_79 = l_myMacro____x40_Init_Tactics___hyg_720____closed__14;
x_80 = lean_array_push(x_78, x_79);
x_81 = l_Lean_Elab_Term_expandShow___closed__12;
x_82 = lean_array_push(x_81, x_50);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_41);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_80, x_83);
x_85 = l_Lean_Elab_Term_expandHave___closed__1;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_3);
return x_87;
}
}
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSuffices(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Elab_Term_expandSuffices___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_usize(x_4, 2);
lean_dec(x_4);
x_11 = lean_box_usize(x_10);
x_12 = lean_apply_6(x_2, x_8, x_9, x_11, x_7, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_apply_1(x_3, x_1);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `parser!` macro, it must be used in definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `parser!` macro, unexpected declaration name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.leadingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leadingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OrElse.orElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OrElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.mkAntiquot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAntiquot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_16);
x_17 = l_Lean_extractMacroScopes(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_19 = lean_ctor_get(x_17, 3);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Init_LeanInit_0__Lean_quoteName(x_16);
x_22 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_23 = l_Lean_mkStxStrLit(x_20, x_22);
lean_dec(x_20);
x_24 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
x_31 = l_Lean_addMacroScope(x_28, x_30, x_25);
x_32 = lean_box(0);
x_33 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
x_34 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13;
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_34);
x_36 = l_Array_empty___closed__1;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_array_push(x_36, x_21);
lean_inc(x_38);
x_39 = lean_array_push(x_38, x_1);
x_40 = lean_array_push(x_39, x_2);
x_41 = l_Lean_nullKind___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_array_push(x_37, x_42);
x_44 = l_Lean_mkAppStx___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(x_19, x_32);
lean_dec(x_19);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_38);
x_47 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_3);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_48);
lean_inc(x_52);
x_54 = l_Lean_addMacroScope(x_52, x_53, x_48);
x_55 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_56 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_array_push(x_36, x_57);
x_59 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_48);
lean_inc(x_52);
x_60 = l_Lean_addMacroScope(x_52, x_59, x_48);
x_61 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_62 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_22);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_array_push(x_36, x_63);
x_65 = lean_array_push(x_36, x_23);
x_66 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__42;
x_67 = l_Lean_addMacroScope(x_52, x_66, x_48);
x_68 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__41;
x_69 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__44;
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_22);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_array_push(x_65, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_41);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_64, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_44);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_36, x_74);
x_76 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_41);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_80 = lean_array_push(x_79, x_78);
x_81 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_82 = lean_array_push(x_80, x_81);
x_83 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_array_push(x_36, x_84);
x_86 = lean_array_push(x_85, x_45);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_41);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_58, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_44);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_50, 0, x_89);
return x_50;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_90 = lean_ctor_get(x_50, 0);
x_91 = lean_ctor_get(x_50, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_50);
x_92 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_48);
lean_inc(x_90);
x_93 = l_Lean_addMacroScope(x_90, x_92, x_48);
x_94 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_95 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_22);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_95);
x_97 = lean_array_push(x_36, x_96);
x_98 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_48);
lean_inc(x_90);
x_99 = l_Lean_addMacroScope(x_90, x_98, x_48);
x_100 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_101 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_22);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_101);
x_103 = lean_array_push(x_36, x_102);
x_104 = lean_array_push(x_36, x_23);
x_105 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__42;
x_106 = l_Lean_addMacroScope(x_90, x_105, x_48);
x_107 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__41;
x_108 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___closed__44;
x_109 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_109, 0, x_22);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_108);
x_110 = lean_array_push(x_104, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_41);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_array_push(x_103, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_44);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_36, x_113);
x_115 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_116 = lean_array_push(x_114, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_41);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_119 = lean_array_push(x_118, x_117);
x_120 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_121 = lean_array_push(x_119, x_120);
x_122 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_array_push(x_36, x_123);
x_125 = lean_array_push(x_124, x_45);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_41);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_array_push(x_97, x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_44);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_91);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_130 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_3);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_132);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_131);
lean_inc(x_135);
x_137 = l_Lean_addMacroScope(x_135, x_136, x_131);
x_138 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_139 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_22);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_139);
x_141 = lean_array_push(x_36, x_140);
x_142 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_131);
lean_inc(x_135);
x_143 = l_Lean_addMacroScope(x_135, x_142, x_131);
x_144 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_145 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_22);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set(x_146, 2, x_143);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_array_push(x_36, x_146);
x_148 = lean_array_push(x_36, x_23);
x_149 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
x_150 = l_Lean_addMacroScope(x_135, x_149, x_131);
x_151 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
x_152 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
x_153 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_153, 0, x_22);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_152);
x_154 = lean_array_push(x_36, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_41);
lean_ctor_set(x_155, 1, x_38);
x_156 = lean_array_push(x_154, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_44);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_push(x_36, x_157);
x_159 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_160 = lean_array_push(x_158, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_41);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_163 = lean_array_push(x_162, x_161);
x_164 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_165 = lean_array_push(x_163, x_164);
x_166 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_array_push(x_148, x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_41);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_147, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_44);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_array_push(x_36, x_171);
x_173 = lean_array_push(x_172, x_159);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_41);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_push(x_162, x_174);
x_176 = lean_array_push(x_175, x_164);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_array_push(x_36, x_177);
x_179 = lean_array_push(x_178, x_45);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_41);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_push(x_141, x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_44);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_133, 0, x_182);
return x_133;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_183 = lean_ctor_get(x_133, 0);
x_184 = lean_ctor_get(x_133, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_133);
x_185 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_131);
lean_inc(x_183);
x_186 = l_Lean_addMacroScope(x_183, x_185, x_131);
x_187 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_188 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_189 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_189, 0, x_22);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_186);
lean_ctor_set(x_189, 3, x_188);
x_190 = lean_array_push(x_36, x_189);
x_191 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_131);
lean_inc(x_183);
x_192 = l_Lean_addMacroScope(x_183, x_191, x_131);
x_193 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_194 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_195 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_195, 0, x_22);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_195, 2, x_192);
lean_ctor_set(x_195, 3, x_194);
x_196 = lean_array_push(x_36, x_195);
x_197 = lean_array_push(x_36, x_23);
x_198 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
x_199 = l_Lean_addMacroScope(x_183, x_198, x_131);
x_200 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
x_201 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
x_202 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_202, 0, x_22);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_199);
lean_ctor_set(x_202, 3, x_201);
x_203 = lean_array_push(x_36, x_202);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_41);
lean_ctor_set(x_204, 1, x_38);
x_205 = lean_array_push(x_203, x_204);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_44);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_array_push(x_36, x_206);
x_208 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_209 = lean_array_push(x_207, x_208);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_41);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_212 = lean_array_push(x_211, x_210);
x_213 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_214 = lean_array_push(x_212, x_213);
x_215 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_array_push(x_197, x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_41);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_array_push(x_196, x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_44);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_array_push(x_36, x_220);
x_222 = lean_array_push(x_221, x_208);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_41);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_array_push(x_211, x_223);
x_225 = lean_array_push(x_224, x_213);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_36, x_226);
x_228 = lean_array_push(x_227, x_45);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_41);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_push(x_190, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_44);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_184);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_233 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6;
x_234 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_233, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_234;
}
}
}
}
lean_object* l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser!");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_numLitKind;
x_2 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__3;
x_3 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_4 = l_Lean_mkStxLit(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Syntax_getArgs(x_1);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; uint8_t x_33; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_32 = l_Lean_nullKind___closed__2;
lean_inc(x_18);
x_33 = l_Lean_Syntax_isOfKind(x_18, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_19 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = l_Lean_Syntax_getArgs(x_18);
x_36 = lean_array_get_size(x_35);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_19 = x_39;
goto block_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
x_40 = lean_unsigned_to_nat(2u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
lean_dec(x_1);
x_42 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4;
x_43 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_42, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_43;
}
}
block_31:
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_19);
x_20 = l_Lean_nullKind___closed__2;
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArgs(x_18);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_29 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_30;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserMacro___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabParserMacro___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabParserMacro___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserMacro), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabParserMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `tparser!` macro, it must be used in definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.trailingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trailingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l___private_Init_LeanInit_0__Lean_quoteName(x_16);
x_18 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_25 = l_Lean_addMacroScope(x_23, x_24, x_19);
x_26 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_27 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
x_28 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10;
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Array_empty___closed__1;
x_31 = lean_array_push(x_30, x_29);
x_32 = lean_array_push(x_30, x_17);
x_33 = lean_array_push(x_32, x_1);
x_34 = lean_array_push(x_33, x_2);
x_35 = l_Lean_nullKind___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_31, x_36);
x_38 = l_Lean_mkAppStx___closed__8;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_43 = l_Lean_addMacroScope(x_40, x_42, x_19);
x_44 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_45 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
x_46 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10;
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Array_empty___closed__1;
x_49 = lean_array_push(x_48, x_47);
x_50 = lean_array_push(x_48, x_17);
x_51 = lean_array_push(x_50, x_1);
x_52 = lean_array_push(x_51, x_2);
x_53 = l_Lean_nullKind___closed__2;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_array_push(x_49, x_54);
x_56 = l_Lean_mkAppStx___closed__8;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
return x_58;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tparser!");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Syntax_getArgs(x_1);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; uint8_t x_33; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_32 = l_Lean_nullKind___closed__2;
lean_inc(x_18);
x_33 = l_Lean_Syntax_isOfKind(x_18, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_19 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = l_Lean_Syntax_getArgs(x_18);
x_36 = lean_array_get_size(x_35);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_19 = x_39;
goto block_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
x_40 = lean_unsigned_to_nat(2u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
lean_dec(x_1);
x_42 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4;
x_43 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_42, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_43;
}
}
block_31:
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_19);
x_20 = l_Lean_nullKind___closed__2;
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArgs(x_18);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabArrow___spec__1___rarg(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_29 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_30;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabTParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTParserMacro___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabTParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabTParserMacro___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabTParserMacro___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTParserMacro), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabTParserMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_nativeRefl");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2;
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_mkAuxName(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
x_16 = lean_box(1);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_7);
lean_inc(x_3);
x_20 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid macro application, term contains free variables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasFVar(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = l_Lean_indentExpr(x_1);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid macro application, term contains metavariables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_elabTermAndSynthesize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_hasMVar(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lean_indentExpr(x_11);
x_17 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeRefl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to reduce term at `nativeRefl!` macro application");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofReduceNat");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofReduceBool");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__1;
x_15 = l_Lean_Expr_isConstOf(x_1, x_14);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lean_mkConst(x_12, x_16);
if (x_15 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3;
lean_inc(x_17);
x_47 = l_Lean_mkApp(x_46, x_17);
x_48 = l_Lean_Meta_reduceNative_x3f(x_47, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5;
x_18 = x_51;
x_19 = x_49;
x_20 = x_50;
goto block_45;
}
else
{
uint8_t x_52; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6;
lean_inc(x_17);
x_57 = l_Lean_mkApp(x_56, x_17);
x_58 = l_Lean_Meta_reduceNative_x3f(x_57, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8;
x_18 = x_61;
x_19 = x_59;
x_20 = x_60;
goto block_45;
}
else
{
uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
block_45:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_27, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_mkConst(x_18, x_16);
lean_inc(x_27);
x_32 = l_Lean_mkApp3(x_31, x_17, x_27, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_2, x_27, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_32, x_34, x_6, x_7, x_8, x_9, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_11);
if (x_66 == 0)
{
return x_11;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `nativeRefl!` macro application, term must have type `Nat` or `Bool`");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabNativeRefl___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__1;
x_23 = l_Lean_Expr_isConstOf(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Literal_type___closed__2;
x_25 = l_Lean_Expr_isConstOf(x_20, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_14);
x_26 = l_Lean_indentExpr(x_20);
x_27 = l_Lean_Elab_Term_elabNativeRefl___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Term_elabNativeRefl___lambda__1(x_20, x_14, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_4);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Term_elabNativeRefl___lambda__1(x_20, x_14, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_4);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabNativeRefl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabNativeRefl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nativeRefl");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeRefl___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid macro, expected type is not available");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected type must not contain free or meta variables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3;
x_12 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = 1;
x_16 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_instantiateMVarsImp(x_14, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_35 = l_Lean_Expr_hasFVar(x_21);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_21);
if (x_36 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_free_object(x_19);
x_23 = x_16;
goto block_34;
}
}
else
{
lean_free_object(x_19);
x_23 = x_16;
goto block_34;
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_23);
x_24 = l_Lean_indentExpr(x_21);
x_25 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_51; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_51 = l_Lean_Expr_hasFVar(x_37);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Expr_hasMVar(x_37);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
return x_53;
}
else
{
x_39 = x_16;
goto block_50;
}
}
else
{
x_39 = x_16;
goto block_50;
}
block_50:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
x_40 = l_Lean_indentExpr(x_37);
x_41 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
return x_19;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_19, 0);
x_56 = lean_ctor_get(x_19, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_19);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_9);
if (x_62 == 0)
{
return x_9;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_9, 0);
x_64 = lean_ctor_get(x_9, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_9);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_box(0);
x_11 = l_Lean_mkAppStx___closed__9;
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Lean_Meta_mkDecide___rarg___closed__1;
x_15 = l_Lean_Meta_mkAppOptM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__2(x_14, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeDecide___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1;
lean_inc(x_6);
x_17 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_20, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkConst(x_18, x_15);
x_25 = l_Lean_Elab_Term_elabNativeDecide___rarg___closed__2;
x_26 = l_Lean_mkApp3(x_25, x_24, x_20, x_22);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_26, x_10, x_4, x_5, x_6, x_7, x_23);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabNativeDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeDecide___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabNativeDecide___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_elabNativeDecide(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nativeDecide");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeDecide___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDecide___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDecide___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabDecide___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_instantiateMVarsImp(x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_elabDecide___rarg___closed__1;
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_19, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Elab_Term_elabDecide___rarg___closed__2;
x_24 = l_Lean_mkApp3(x_23, x_10, x_18, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = l_Lean_Elab_Term_elabDecide___rarg___closed__2;
x_28 = l_Lean_mkApp3(x_27, x_10, x_18, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDecide___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabDecide___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_elabDecide(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDecide___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_myMacro____x40_Init_Tactics___hyg_186____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandInfix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_mkAppStx___closed__9;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_mkAppStx(x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_expandInfix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandInfix(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandInfixOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_mkCIdentFrom(x_6, x_1);
lean_dec(x_6);
x_8 = l_Lean_Elab_Term_expandInfix(x_7, x_2, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_expandInfixOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandInfixOp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandPrefixOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_mkCIdentFrom(x_8, x_1);
lean_dec(x_8);
x_10 = l_Lean_mkOptionalNode___closed__2;
x_11 = lean_array_push(x_10, x_6);
x_12 = l_Lean_mkAppStx(x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_expandPrefixOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandPrefixOp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandProd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Init_LeanInit___instance__19___rarg___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandProd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandProd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandProd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("prod");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandProd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandProd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandProd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandProd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandProd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandProd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandProd___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_ExpandFComp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Function");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ExpandFComp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_ExpandFComp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_ExpandFComp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("comp");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ExpandFComp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_ExpandFComp___closed__2;
x_2 = l_Lean_Elab_Term_ExpandFComp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_ExpandFComp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_ExpandFComp___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_ExpandFComp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_ExpandFComp(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fcomp");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ExpandFComp___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_ExpandFComp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__9;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAdd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAdd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAdd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAdd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandAdd___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAdd___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSub(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_evalNat___closed__15;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSub(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSub___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_evalNat___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSub___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSub___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSub(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandSub___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSub___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandMul(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_evalNat___closed__8;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMul(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMul___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_evalNat___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMul___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMul___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandMul(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandMul___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandMul___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Div");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDiv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDiv___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDiv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDiv___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandDiv___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandDiv(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDiv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDiv___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandDiv___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandDiv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandDiv___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandDiv___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Mod");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMod___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandMod___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMod___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMod___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandMod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandMod___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMod(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMod___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMod___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMod___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandMod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandMod___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandMod___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ModN");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandModN___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandModN___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandModN___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modn");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandModN___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandModN___closed__2;
x_2 = l_Lean_Elab_Term_expandModN___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandModN(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandModN___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandModN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandModN(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modN");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandModN___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandModN___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandModN___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandModN___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandModN(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandModN___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandModN___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandPow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Pow");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandPow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandPow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandPow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pow");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandPow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandPow___closed__2;
x_2 = l_Lean_Elab_Term_expandPow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandPow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandPow___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandPow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandPow(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandPow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandPow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandPow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandPow___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandPow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandPow___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandPow___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandLE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_mkLe___rarg___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandLE(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandLE___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("le");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandLE___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandLE___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandLE___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLE___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandLE(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandLE___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandLE___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandGE___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("GreaterEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandGE___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandGE___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandGE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandGE___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandGE(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandGE___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ge");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandGE___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandGE___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandGE___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandGE___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandGE(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandGE___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandGE___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandLT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_mkLt___rarg___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandLT(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandLT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lt");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandLT___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandLT___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandLT___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLT___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandLT(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandLT___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandLT___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandGT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Greater");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandGT___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandGT___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandGT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandGT___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandGT(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandGT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("gt");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandGT___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandGT___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandGT___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandGT___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandGT(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandGT___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandGT___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_eq_x3f___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandEq(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandEq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Term_expandEq___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandNe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Ne");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandNe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandNe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandNe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandNe___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandNe(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandNe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ne");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandNe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandNe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandNe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandNe___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandNe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandNe___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandNe___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("BEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandBEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandBEq___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandBEq___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandBEq(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandBEq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandBEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__2___closed__13;
x_4 = l___regBuiltin_Lean_Elab_Term_expandBEq___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBNe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bne");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBNe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandBNe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandBNe___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandBNe(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBNe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandBNe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBNe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandBNe___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandBNe___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandBNe___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_heq_x3f___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandHEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandHEq(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandHEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heq");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandHEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandHEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandHEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHEq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandHEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandHEq___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandHEq___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEquiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Equiv");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEquiv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEquiv___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEquiv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandEquiv___closed__2;
x_2 = l_Lean_Elab_Term_expandEquiv___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandEquiv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandEquiv___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandEquiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandEquiv(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equiv");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandEquiv___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandEquiv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandAnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandAnd___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAnd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("and");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAnd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandAnd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAnd___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Or");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandOr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandOr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandOr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandOr___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandOr(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("or");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandOr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOr___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandOr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandOr___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandOr___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandIff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_iff_x3f___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandIff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandIff(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandIff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("iff");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandIff___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandIff___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandIff___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandIff___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandIff(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandIff___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandIff___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBAnd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandBAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandBAnd___closed__1;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandBAnd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandBAnd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandBAnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__2___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_expandBAnd___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBOr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_expandOr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandBOr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandBOr___closed__1;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandBOr(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bor");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBOr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandBOr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBOr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandBOr___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandBOr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandBOr___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandBOr___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Append");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAppend___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandAppend___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAppend___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandAppend___closed__2;
x_2 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandAppend(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandAppend___closed__3;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAppend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAppend(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAppend___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAppend___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandCons(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandCons___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandCons(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandCons___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandCons___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandCons___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandCons(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandCons___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandCons___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAndThen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("AndThen");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAndThen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandAndThen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAndThen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andThen");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAndThen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandAndThen___closed__2;
x_2 = l_Lean_Elab_Term_expandAndThen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandAndThen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandAndThen___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAndThen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAndThen(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andthen");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAndThen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndThen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandBind(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bindOp");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandBind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandBind___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandBind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandBind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandBind___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Seq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSeq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandSeq___closed__2;
x_2 = l_Lean_Elab_Term_expandSeq___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandSeq___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSeq(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSeq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandSeq___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSeq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandSeq___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSeq___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SeqLeft");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqLeft___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSeqLeft___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqLeft___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seqLeft");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqLeft___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandSeqLeft___closed__2;
x_2 = l_Lean_Elab_Term_expandSeqLeft___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSeqLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandSeqLeft___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSeqLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSeqLeft(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandSeqLeft___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSeqLeft___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SeqRight");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqRight___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSeqRight___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqRight___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seqRight");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSeqRight___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandSeqRight___closed__2;
x_2 = l_Lean_Elab_Term_expandSeqRight___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSeqRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandSeqRight___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSeqRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSeqRight(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandSeqRight___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSeqRight___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSeqRight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMap___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Functor");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandMap___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMap___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("map");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMap___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMap___closed__2;
x_2 = l_Lean_Elab_Term_expandMap___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandMap___closed__4;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMap(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandMap___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMap___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMap___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandMap___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandMap___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMapRev___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mapRev");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMapRev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMap___closed__2;
x_2 = l_Lean_Elab_Term_expandMapRev___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandMapRev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandMapRev___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandMapRev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMapRev(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandMapRev___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMapRev___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandMapRev(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandOrElse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandOrElse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandOrElse(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_myMacro____x40_Init_Tactics___hyg_720____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOrElse___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrElse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandOrM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orM");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandOrM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandOrM___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandOrM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandOrM___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandOrM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandOrM(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOrM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandOrM___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandOrM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOrM___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandOrM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandOrM___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandOrM___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAndM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andM");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAndM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandAndM___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandAndM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandAndM___closed__2;
x_5 = l_Lean_Elab_Term_expandInfixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAndM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAndM(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAndM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandAndM___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAndM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAndM___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAndM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandAndM___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAndM___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandNot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandNot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandNot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandNot___closed__2;
x_5 = l_Lean_Elab_Term_expandPrefixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandNot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandNot(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandNot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandNot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandNot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandNot___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandNot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandNot___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandNot___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandBNot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_expandNot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandBNot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandBNot___closed__1;
x_5 = l_Lean_Elab_Term_expandPrefixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandBNot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandBNot(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBNot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bnot");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandBNot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandBNot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandBNot___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandBNot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandBNot___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandBNot___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUMinus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Neg");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUMinus___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandUMinus___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUMinus___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("neg");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUMinus___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandUMinus___closed__2;
x_2 = l_Lean_Elab_Term_expandUMinus___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandUMinus(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_expandUMinus___closed__4;
x_5 = l_Lean_Elab_Term_expandPrefixOp(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandUMinus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandUMinus(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uminus");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandUMinus___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandUMinus(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabPanic_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabPanic_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_Syntax_getPos(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_FileMap_toPosition(x_8, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_FileMap_toPosition(x_8, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_Elab_Term_elabPanic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 6);
lean_inc(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_4, 6, x_14);
x_15 = 1;
x_16 = l_Lean_Elab_Term_elabTerm(x_3, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
x_23 = lean_ctor_get(x_4, 6);
x_24 = lean_ctor_get(x_4, 7);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_20);
lean_ctor_set(x_29, 4, x_21);
lean_ctor_set(x_29, 5, x_22);
lean_ctor_set(x_29, 6, x_28);
lean_ctor_set(x_29, 7, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*8, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*8 + 1, x_26);
x_30 = 1;
x_31 = l_Lean_Elab_Term_elabTerm(x_3, x_2, x_30, x_29, x_5, x_6, x_7, x_8, x_9, x_10);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panicWithPos");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabPanic___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panicWithPosWithDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabPanic___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabPanic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_elabPanic___closed__4;
x_29 = l_Lean_addMacroScope(x_26, x_28, x_23);
x_30 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_31 = l_Lean_Elab_Term_elabPanic___closed__3;
x_32 = l_Lean_Elab_Term_elabPanic___closed__6;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Array_empty___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_environment_main_module(x_18);
x_37 = l_System_FilePath_dirName___closed__1;
x_38 = l_Lean_Name_toStringWithSep(x_37, x_36);
x_39 = l_Lean_mkStxStrLit(x_38, x_30);
lean_dec(x_38);
x_40 = lean_array_push(x_34, x_39);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = l_Nat_repr(x_41);
x_43 = l_Lean_numLitKind;
x_44 = l_Lean_mkStxLit(x_43, x_42, x_30);
x_45 = lean_array_push(x_40, x_44);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = l_Nat_repr(x_46);
x_48 = l_Lean_mkStxLit(x_43, x_47, x_30);
x_49 = lean_array_push(x_45, x_48);
x_50 = lean_array_push(x_49, x_11);
x_51 = l_Lean_nullKind___closed__2;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_array_push(x_35, x_52);
x_54 = l_Lean_mkAppStx___closed__8;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_Term_elabPanic___lambda__1(x_1, x_2, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_dec(x_19);
x_58 = lean_ctor_get(x_20, 0);
lean_inc(x_58);
lean_dec(x_20);
x_59 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Elab_Term_elabPanic___closed__10;
x_66 = l_Lean_addMacroScope(x_63, x_65, x_60);
x_67 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_68 = l_Lean_Elab_Term_elabPanic___closed__9;
x_69 = l_Lean_Elab_Term_elabPanic___closed__12;
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_69);
x_71 = l_Array_empty___closed__1;
x_72 = lean_array_push(x_71, x_70);
x_73 = lean_environment_main_module(x_18);
x_74 = l_System_FilePath_dirName___closed__1;
x_75 = l_Lean_Name_toStringWithSep(x_74, x_73);
x_76 = l_Lean_mkStxStrLit(x_75, x_67);
lean_dec(x_75);
x_77 = lean_array_push(x_71, x_76);
x_78 = l_Lean_Name_toStringWithSep(x_74, x_58);
x_79 = l_Lean_mkStxStrLit(x_78, x_67);
lean_dec(x_78);
x_80 = lean_array_push(x_77, x_79);
x_81 = lean_ctor_get(x_13, 0);
lean_inc(x_81);
x_82 = l_Nat_repr(x_81);
x_83 = l_Lean_numLitKind;
x_84 = l_Lean_mkStxLit(x_83, x_82, x_67);
x_85 = lean_array_push(x_80, x_84);
x_86 = lean_ctor_get(x_13, 1);
lean_inc(x_86);
lean_dec(x_13);
x_87 = l_Nat_repr(x_86);
x_88 = l_Lean_mkStxLit(x_83, x_87, x_67);
x_89 = lean_array_push(x_85, x_88);
x_90 = lean_array_push(x_89, x_11);
x_91 = l_Lean_nullKind___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_72, x_92);
x_94 = l_Lean_mkAppStx___closed__8;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Elab_Term_elabPanic___lambda__1(x_1, x_2, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
return x_96;
}
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panic");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panic!");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"unreachable code has been reached\"");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_strLitKind___closed__2;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__3;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2;
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandUnreachable___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandUnreachable(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandUnreachable___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAssert_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandAssert_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAssert_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__4;
x_2 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"assertion violation\"");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandAssert___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandAssert___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_strLitKind___closed__2;
x_2 = l_Lean_Elab_Term_expandAssert___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandAssert___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandAssert___closed__6;
x_2 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Term_expandAssert___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_2 = l_Lean_Elab_Term_expandAssert___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandAssert___closed__9;
x_2 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_2 = l_Lean_Elab_Term_expandAssert___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__3;
x_2 = l_Lean_Elab_Term_expandAssert___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2;
x_2 = l_Lean_Elab_Term_expandAssert___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"assertion violation: \"");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_Elab_Term_expandAssert___closed__14;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandAssert___closed__15;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_strLitKind___closed__2;
x_2 = l_Lean_Elab_Term_expandAssert___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandAssert___closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandAssert___closed__18;
x_2 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandAssert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_inc(x_5);
x_8 = l_Lean_Syntax_reprint(x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = l_Lean_Elab_Term_expandAssert___closed__1;
x_10 = lean_array_push(x_9, x_5);
x_11 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__12;
x_12 = lean_array_push(x_10, x_11);
x_13 = lean_array_push(x_12, x_7);
x_14 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__14;
x_15 = lean_array_push(x_13, x_14);
x_16 = l_Lean_Elab_Term_expandAssert___closed__13;
x_17 = lean_array_push(x_15, x_16);
x_18 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l_Lean_Elab_Term_expandAssert___closed__1;
x_23 = lean_array_push(x_22, x_5);
x_24 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__12;
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_array_push(x_25, x_7);
x_27 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__14;
x_28 = lean_array_push(x_26, x_27);
x_29 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_30 = l_Lean_mkStxStrLit(x_21, x_29);
lean_dec(x_21);
x_31 = l_Lean_Elab_Term_expandAssert___closed__19;
x_32 = lean_array_push(x_31, x_30);
x_33 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__1___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Array_empty___closed__1;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_38 = lean_array_push(x_36, x_37);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_42 = lean_array_push(x_41, x_40);
x_43 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_44 = lean_array_push(x_42, x_43);
x_45 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__3;
x_48 = lean_array_push(x_47, x_46);
x_49 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_array_push(x_28, x_50);
x_52 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_compileStxMatch___lambda__1___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAssert(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assert");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAssert___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAssert___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dbgTrace");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__2___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___kind_tactic____x40_Init_Tactics___hyg_2____closed__2;
x_2 = l___kind_tactic____x40_Init_Tactics___hyg_461____closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__9;
x_2 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__10;
x_2 = l___kind_tactic____x40_Init_Tactics___hyg_2____closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__11;
x_2 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_109____closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__12;
x_2 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__13;
x_2 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__14;
x_2 = l_Lean_Name_hasMacroScopes___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandDbgTrace___closed__15;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__16;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_inc(x_5);
x_8 = l_Lean_Syntax_getKind(x_5);
x_9 = l_Lean_interpolatedStrKind;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_expandDbgTrace___closed__4;
lean_inc(x_11);
lean_inc(x_12);
x_14 = l_Lean_addMacroScope(x_12, x_13, x_11);
x_15 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_16 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_17 = l_Lean_Elab_Term_expandDbgTrace___closed__6;
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__2___closed__4;
x_22 = l_Lean_addMacroScope(x_12, x_21, x_11);
x_23 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____lambda__2___closed__3;
x_24 = l_Lean_Elab_Term_expandDbgTrace___closed__8;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_array_push(x_19, x_25);
x_27 = lean_array_push(x_19, x_5);
x_28 = l_Lean_nullKind___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_26, x_29);
x_31 = l_Lean_mkAppStx___closed__8;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_array_push(x_19, x_32);
x_34 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_38 = lean_array_push(x_37, x_36);
x_39 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_40 = lean_array_push(x_38, x_39);
x_41 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_array_push(x_19, x_42);
x_44 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
x_45 = lean_array_push(x_44, x_7);
x_46 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_49 = lean_array_push(x_48, x_47);
x_50 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_43, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_push(x_20, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l_Lean_Elab_Term_expandDbgTrace___closed__4;
x_60 = l_Lean_addMacroScope(x_58, x_59, x_57);
x_61 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_62 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_63 = l_Lean_Elab_Term_expandDbgTrace___closed__6;
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_63);
x_65 = l_Array_empty___closed__1;
x_66 = lean_array_push(x_65, x_64);
x_67 = l_Lean_Elab_Term_expandDbgTrace___closed__18;
x_68 = lean_array_push(x_67, x_5);
x_69 = l_Lean_Elab_Term_expandDbgTrace___closed__16;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_array_push(x_65, x_70);
x_72 = l_myMacro____x40_Init_Tactics___hyg_720____closed__18;
x_73 = lean_array_push(x_71, x_72);
x_74 = l_Lean_nullKind___closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_77 = lean_array_push(x_76, x_75);
x_78 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_79 = lean_array_push(x_77, x_78);
x_80 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_65, x_81);
x_83 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
x_84 = lean_array_push(x_83, x_7);
x_85 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_88 = lean_array_push(x_87, x_86);
x_89 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_82, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_74);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_push(x_66, x_92);
x_94 = l_Lean_mkAppStx___closed__8;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_3);
return x_96;
}
}
}
lean_object* l_Lean_Elab_Term_expandDbgTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandDbgTrace(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandDbgTrace___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandSorry___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSorry___rarg___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Init_Data_Repr___instance__2___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Init_Data_Repr___instance__2___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandSorry___rarg___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSorry___rarg___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSorry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
lean_inc(x_3);
lean_inc(x_4);
x_6 = l_Lean_addMacroScope(x_4, x_5, x_3);
x_7 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_8 = l_Lean_Elab_Term_expandSorry___rarg___closed__2;
x_9 = l_Lean_Elab_Term_expandSorry___rarg___closed__4;
x_10 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_9);
x_11 = l_Array_empty___closed__1;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_setOptionFromString___closed__5;
x_14 = l_Lean_addMacroScope(x_4, x_13, x_3);
x_15 = l_Lean_Elab_Term_expandSorry___rarg___closed__6;
x_16 = l_Lean_Elab_Term_expandSorry___rarg___closed__8;
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12;
x_19 = lean_array_push(x_18, x_17);
x_20 = l_Lean_nullKind___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_push(x_12, x_21);
x_23 = l_Lean_mkAppStx___closed__8;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
}
lean_object* l_Lean_Elab_Term_expandSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSorry___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSorry___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_expandSorry(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSorry___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_myMacro____x40_Init_Tactics___hyg_338____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EmptyCollection.emptyCollection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandEmptyC___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandEmptyC___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandEmptyC___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EmptyCollection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("emptyCollection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandEmptyC___closed__5;
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandEmptyC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_10 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_expandEmptyC___closed__7;
x_17 = l_Lean_addMacroScope(x_14, x_16, x_11);
x_18 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_19 = l_Lean_Elab_Term_expandEmptyC___closed__3;
x_20 = l_Lean_Elab_Term_expandEmptyC___closed__9;
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_20);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 6);
lean_inc(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_3, 6, x_25);
x_26 = 1;
x_27 = l_Lean_Elab_Term_elabTerm(x_21, x_2, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get(x_3, 4);
x_33 = lean_ctor_get(x_3, 5);
x_34 = lean_ctor_get(x_3, 6);
x_35 = lean_ctor_get(x_3, 7);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
lean_inc(x_21);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 4, x_32);
lean_ctor_set(x_40, 5, x_33);
lean_ctor_set(x_40, 6, x_39);
lean_ctor_set(x_40, 7, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*8 + 1, x_37);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTerm(x_21, x_2, x_41, x_40, x_4, x_5, x_6, x_7, x_8, x_15);
return x_42;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandEmptyC), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__12;
x_4 = l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod.mk");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkPairs_loop___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_mkPairs_loop___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_mkPairs_loop___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Init_LeanInit___instance__19___rarg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkPairs_loop___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = l_Lean_Init_LeanInit___instance__9;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = l_Lean_Init_LeanInit___instance__19___rarg___closed__4;
x_16 = l_Lean_addMacroScope(x_14, x_15, x_13);
x_17 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_18 = l_Lean_Elab_Term_mkPairs_loop___closed__3;
x_19 = l_Lean_Elab_Term_mkPairs_loop___closed__5;
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean_array_push(x_21, x_20);
x_23 = lean_array_push(x_21, x_12);
x_24 = lean_array_push(x_23, x_3);
x_25 = l_Lean_nullKind___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_22, x_26);
x_28 = l_Lean_mkAppStx___closed__8;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_2 = x_10;
x_3 = x_29;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkPairs_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_mkPairs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_8 = l_Lean_Elab_Term_mkPairs_loop(x_1, x_6, x_7, x_2, x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkPairs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
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
uint8_t l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2;
x_7 = lean_name_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(x_3, x_14, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 < x_1;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = x_11;
lean_inc(x_5);
x_15 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(x_14, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = x_2 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_13, x_2, x_22);
x_2 = x_21;
x_3 = x_23;
x_4 = x_19;
x_6 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
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
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2;
x_13 = lean_name_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_get_size(x_6);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = x_6;
x_17 = lean_box_usize(x_15);
x_18 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed), 6, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
x_20 = x_19;
x_21 = lean_apply_3(x_20, x_2, x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_23, 0, x_1);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_1);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
lean_dec(x_3);
x_43 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__11;
x_44 = l_Lean_addMacroScope(x_42, x_43, x_4);
x_45 = lean_box(0);
x_46 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_47 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__10;
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
lean_inc(x_48);
x_49 = lean_array_push(x_2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_1);
x_52 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2;
x_53 = lean_name_eq(x_5, x_52);
if (x_53 == 0)
{
lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_array_get_size(x_6);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = x_6;
x_57 = lean_box_usize(x_55);
x_58 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
x_59 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed), 6, 3);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
lean_closure_set(x_59, 2, x_56);
x_60 = x_59;
x_61 = lean_apply_3(x_60, x_2, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_65);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_73 = x_61;
} else {
 lean_dec_ref(x_61);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_5);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_4, x_75);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__11;
x_79 = l_Lean_addMacroScope(x_77, x_78, x_4);
x_80 = lean_box(0);
x_81 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_82 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_474____closed__10;
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_80);
lean_inc(x_83);
x_84 = lean_array_push(x_2, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_76);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_4);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_3);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_4);
return x_90;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(x_1, x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_append___rarg(x_7, x_12);
lean_dec(x_12);
x_14 = l_Lean_nullKind___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_array_push(x_7, x_15);
x_17 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
x_18 = lean_array_push(x_16, x_17);
x_19 = lean_array_push(x_18, x_11);
x_20 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_8, 0, x_26);
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Array_append___rarg(x_7, x_30);
lean_dec(x_30);
x_32 = l_Lean_nullKind___closed__2;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_7, x_33);
x_35 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_array_push(x_36, x_29);
x_38 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_28);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
return x_8;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_37 = lean_st_ref_get(x_8, x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
x_46 = lean_st_ref_get(x_8, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_40);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_50, 0, x_40);
x_51 = x_50;
x_52 = lean_environment_main_module(x_40);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_44);
lean_ctor_set(x_53, 4, x_45);
lean_inc(x_1);
x_54 = l_Lean_Elab_Term_expandCDot_x3f(x_1, x_53, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_8, x_48);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 1);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_56);
x_62 = lean_st_ref_set(x_8, x_58, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_10 = x_55;
x_11 = x_63;
goto block_36;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 2);
x_66 = lean_ctor_get(x_58, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_st_ref_set(x_8, x_67, x_59);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_10 = x_55;
x_11 = x_69;
goto block_36;
}
}
else
{
lean_object* x_70; 
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
lean_dec(x_54);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_71, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_71);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___rarg(x_48);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_36:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_3, 6, x_18);
x_19 = 1;
x_20 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = lean_ctor_get(x_3, 5);
x_27 = lean_ctor_get(x_3, 6);
x_28 = lean_ctor_get(x_3, 7);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_24);
lean_ctor_set(x_33, 4, x_25);
lean_ctor_set(x_33, 5, x_26);
lean_ctor_set(x_33, 6, x_32);
lean_ctor_set(x_33, 7, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 1, x_30);
x_34 = 1;
x_35 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_34, x_33, x_4, x_5, x_6, x_7, x_8, x_11);
return x_35;
}
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parentheses notation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabParen___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabParen___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tupleTail");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_elabParen___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
lean_inc(x_1);
x_35 = l_Lean_Syntax_isOfKind(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = l_Lean_Elab_Term_elabParen___closed__3;
x_37 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_Lean_Syntax_getArgs(x_1);
x_39 = lean_array_get_size(x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Elab_Term_elabParen___closed__3;
x_43 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_160; uint8_t x_161; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
x_160 = l_Lean_nullKind___closed__2;
lean_inc(x_45);
x_161 = l_Lean_Syntax_isOfKind(x_45, x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_box(0);
x_46 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = l_Lean_Syntax_getArgs(x_45);
x_164 = lean_array_get_size(x_163);
lean_dec(x_163);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_nat_dec_eq(x_164, x_165);
lean_dec(x_164);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_box(0);
x_46 = x_167;
goto block_159;
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = l_Lean_Lean_ToExpr___instance__6___lambda__1___closed__3;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_9);
return x_169;
}
}
block_159:
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_46);
x_47 = l_Lean_nullKind___closed__2;
lean_inc(x_45);
x_48 = l_Lean_Syntax_isOfKind(x_45, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l_Lean_Elab_Term_elabParen___closed__3;
x_50 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = l_Lean_Syntax_getArgs(x_45);
x_52 = lean_array_get_size(x_51);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Lean_Elab_Term_elabParen___closed__3;
x_56 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Syntax_getArg(x_45, x_57);
x_59 = l_Lean_Syntax_getArg(x_45, x_44);
lean_dec(x_45);
lean_inc(x_59);
x_60 = l_Lean_Syntax_isOfKind(x_59, x_47);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_61 = l_Lean_Elab_Term_elabParen___closed__3;
x_62 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Syntax_getArgs(x_59);
x_64 = lean_array_get_size(x_63);
lean_dec(x_63);
x_65 = lean_nat_dec_eq(x_64, x_44);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_59);
lean_dec(x_1);
x_66 = lean_nat_dec_eq(x_64, x_57);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_67 = l_Lean_Elab_Term_elabParen___closed__3;
x_68 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_132; uint8_t x_133; 
lean_dec(x_64);
x_70 = l_Lean_Syntax_getArg(x_59, x_57);
lean_dec(x_59);
x_132 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
lean_inc(x_70);
x_133 = l_Lean_Syntax_isOfKind(x_70, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_71 = x_134;
goto block_131;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = l_Lean_Syntax_getArgs(x_70);
x_136 = lean_array_get_size(x_135);
lean_dec(x_135);
x_137 = lean_nat_dec_eq(x_136, x_53);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_box(0);
x_71 = x_138;
goto block_131;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
lean_dec(x_2);
lean_dec(x_1);
x_139 = l_Lean_Syntax_getArg(x_70, x_44);
lean_dec(x_70);
x_140 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType), 8, 1);
lean_closure_set(x_140, 0, x_139);
x_141 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_142 = l_Lean_Elab_Term_withSynthesize___rarg(x_140, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_143);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_145);
x_146 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_58, x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_box(0);
x_150 = l_Lean_Elab_Term_ensureHasType(x_145, x_147, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_148);
return x_150;
}
else
{
uint8_t x_151; 
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = !lean_is_exclusive(x_146);
if (x_151 == 0)
{
return x_146;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_146, 0);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_146);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_155 = !lean_is_exclusive(x_142);
if (x_155 == 0)
{
return x_142;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_142, 0);
x_157 = lean_ctor_get(x_142, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_142);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
block_131:
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_71);
x_72 = l_Lean_Elab_Term_elabParen___closed__5;
lean_inc(x_70);
x_73 = l_Lean_Syntax_isOfKind(x_70, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_74 = l_Lean_Elab_Term_elabParen___closed__3;
x_75 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = l_Lean_Syntax_getArgs(x_70);
x_77 = lean_array_get_size(x_76);
lean_dec(x_76);
x_78 = lean_nat_dec_eq(x_77, x_53);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_70);
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_79 = l_Lean_Elab_Term_elabParen___closed__3;
x_80 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_121; uint8_t x_122; 
x_81 = l_Lean_Syntax_getArg(x_70, x_44);
lean_dec(x_70);
x_82 = l_Lean_Syntax_getArgs(x_81);
lean_dec(x_81);
x_83 = l_Lean_mkOptionalNode___closed__2;
x_84 = lean_array_push(x_83, x_58);
x_121 = lean_array_get_size(x_82);
x_122 = lean_nat_dec_lt(x_57, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_82);
x_123 = l_Array_empty___closed__1;
x_85 = x_123;
goto block_120;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_le(x_121, x_121);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_121);
lean_dec(x_82);
x_125 = l_Array_empty___closed__1;
x_85 = x_125;
goto block_120;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = 0;
x_127 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_128 = l_Array_getEvenElems___rarg___closed__1;
x_129 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_getSepArgs___spec__1(x_82, x_126, x_127, x_128);
lean_dec(x_82);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_85 = x_130;
goto block_120;
}
}
block_120:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_86 = l_Array_append___rarg(x_84, x_85);
lean_dec(x_85);
x_87 = lean_st_ref_get(x_8, x_9);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 2);
lean_inc(x_95);
x_96 = lean_st_ref_get(x_8, x_93);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_90);
x_100 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = x_100;
x_102 = lean_environment_main_module(x_90);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_92);
lean_ctor_set(x_103, 3, x_94);
lean_ctor_set(x_103, 4, x_95);
x_104 = l_Lean_Elab_Term_mkPairs(x_86, x_103, x_99);
lean_dec(x_86);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_take(x_8, x_98);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_108, 1);
lean_dec(x_111);
lean_ctor_set(x_108, 1, x_106);
x_112 = lean_st_ref_set(x_8, x_108, x_109);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_10 = x_105;
x_11 = x_113;
goto block_33;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_108, 0);
x_115 = lean_ctor_get(x_108, 2);
x_116 = lean_ctor_get(x_108, 3);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_108);
x_117 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_106);
lean_ctor_set(x_117, 2, x_115);
lean_ctor_set(x_117, 3, x_116);
x_118 = lean_st_ref_set(x_8, x_117, x_109);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_10 = x_105;
x_11 = x_119;
goto block_33;
}
}
}
}
}
}
}
}
}
}
}
}
block_33:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 6);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_3, 6, x_15);
x_16 = 1;
x_17 = l_Lean_Elab_Term_elabTerm(x_10, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
x_24 = lean_ctor_get(x_3, 6);
x_25 = lean_ctor_get(x_3, 7);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_23);
lean_ctor_set(x_30, 6, x_29);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 1, x_27);
x_31 = 1;
x_32 = l_Lean_Elab_Term_elabTerm(x_10, x_2, x_31, x_30, x_4, x_5, x_6, x_7, x_8, x_11);
return x_32;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_myMacro____x40_Lean_Data_FormatMacro___hyg_40____closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_instantiateMVarsImp(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_isFVar(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
x_16 = l_Lean_Expr_toHeadIndex(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_st_mk_ref(x_19, x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_16, x_18, x_13, x_17, x_21, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_21, x_25);
lean_dec(x_21);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(0);
x_36 = l_Lean_Occurrences_beq(x_3, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_11);
x_37 = l_Lean_Expr_toHeadIndex(x_2);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_st_mk_ref(x_40, x_14);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_37, x_39, x_13, x_38, x_42, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_39);
lean_dec(x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_42, x_46);
lean_dec(x_42);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_42);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = l_Lean_mkOptionalNode___closed__2;
x_57 = lean_array_push(x_56, x_2);
x_58 = lean_expr_abstract(x_13, x_57);
lean_dec(x_57);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_58);
return x_11;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = l_Lean_Expr_isFVar(x_2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = l_Lean_Expr_toHeadIndex(x_2);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_st_mk_ref(x_65, x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_62, x_64, x_59, x_63, x_67, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_64);
lean_dec(x_62);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_67, x_71);
lean_dec(x_67);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_67);
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_box(0);
x_81 = l_Lean_Occurrences_beq(x_3, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = l_Lean_Expr_toHeadIndex(x_2);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_st_mk_ref(x_85, x_60);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_82, x_84, x_59, x_83, x_87, x_6, x_7, x_8, x_9, x_88);
lean_dec(x_84);
lean_dec(x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_get(x_87, x_91);
lean_dec(x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_87);
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
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
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_100 = l_Lean_mkOptionalNode___closed__2;
x_101 = lean_array_push(x_100, x_2);
x_102 = lean_expr_abstract(x_59, x_101);
lean_dec(x_101);
lean_dec(x_59);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_60);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_11);
if (x_104 == 0)
{
return x_11;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_11, 0);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_11);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lambda__1___boxed), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_2, x_15, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_4, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_17, x_5, x_20, x_9, x_10, x_11, x_12, x_21);
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
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_expr_instantiate1(x_1, x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_3, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_elabSubst___lambda__2(x_1, x_5, x_6, x_7, x_8, x_26, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_30 = lean_expr_instantiate1(x_8, x_5);
lean_inc(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_14, 3);
lean_inc(x_35);
x_36 = l_Lean_replaceRef(x_3, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = 1;
lean_inc(x_15);
lean_inc(x_37);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_31);
x_39 = l_Lean_Elab_Term_elabTerm(x_3, x_31, x_38, x_10, x_11, x_12, x_13, x_37, x_15, x_16);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_15);
lean_inc(x_37);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_40);
x_42 = l_Lean_Elab_Term_ensureHasType(x_31, x_40, x_4, x_10, x_11, x_12, x_13, x_37, x_15, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_17 = x_43;
x_18 = x_44;
goto block_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
lean_inc(x_15);
lean_inc(x_37);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_40);
x_47 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_40, x_10, x_11, x_12, x_13, x_37, x_15, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
lean_inc(x_15);
lean_inc(x_37);
lean_inc(x_13);
lean_inc(x_12);
x_51 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_48, x_6, x_50, x_10, x_11, x_12, x_13, x_37, x_15, x_49);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Lean_Expr_hasLooseBVars(x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_45);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_51);
x_56 = lean_box(0);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Lean_Elab_Term_elabSubst___lambda__3(x_53, x_5, x_30, x_45, x_1, x_2, x_7, x_40, x_56, x_10, x_11, x_12, x_13, x_37, x_15, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_17 = x_58;
x_18 = x_59;
goto block_29;
}
else
{
uint8_t x_60; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = l_Lean_Expr_hasLooseBVars(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_45);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_box(0);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_Elab_Term_elabSubst___lambda__3(x_64, x_5, x_30, x_45, x_1, x_2, x_7, x_40, x_68, x_10, x_11, x_12, x_13, x_37, x_15, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_17 = x_70;
x_18 = x_71;
goto block_29;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_51);
if (x_76 == 0)
{
return x_51;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_51, 0);
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_51);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
return x_47;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_47);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_39);
if (x_84 == 0)
{
return x_39;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_39, 0);
x_86 = lean_ctor_get(x_39, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_39);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
block_29:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lambda__1___boxed), 9, 1);
lean_closure_set(x_19, 0, x_8);
x_20 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_21 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_1, x_20, x_2, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_22, x_17, x_7, x_12, x_13, x_14, x_15, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_apply_12(x_1, x_4, x_3, x_15, x_2, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `▸` notation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `▸` notation, argument");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nequality expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `▸` notation, expected type");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndoes contain equation left-hand-side nor right-hand-side");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabSubst___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_tryPostponeIfHasMVars(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_elabSubst___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetDeclCore___spec__1___rarg(x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_Syntax_getArgs(x_1);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetDeclCore___spec__1___rarg(x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = l_Lean_nullKind___closed__2;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetDeclCore___spec__1___rarg(x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Syntax_getArgs(x_25);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetDeclCore___spec__1___rarg(x_13);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_34 = l_Lean_Syntax_getArg(x_25, x_22);
lean_dec(x_25);
x_35 = lean_box(0);
x_36 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Elab_Term_elabTerm(x_23, x_35, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_40 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_Meta_instantiateMVarsImp(x_41, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_44);
x_46 = l_Lean_Meta_matchEq_x3f(x_44, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_34);
lean_dec(x_12);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_indentExpr(x_38);
x_50 = l_Lean_Elab_Term_elabSubst___closed__4;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_44);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Term_elabSubst___closed__6;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
lean_dec(x_47);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_66 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_65, x_7, x_8, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
lean_inc(x_12);
x_70 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_12, x_64, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_34);
lean_inc(x_62);
lean_inc(x_67);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lambda__4___boxed), 16, 4);
lean_closure_set(x_73, 0, x_67);
lean_closure_set(x_73, 1, x_62);
lean_closure_set(x_73, 2, x_34);
lean_closure_set(x_73, 3, x_35);
x_74 = l_Lean_Expr_hasLooseBVars(x_71);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_63);
lean_inc(x_12);
x_75 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_12, x_63, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Expr_hasLooseBVars(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_38);
x_79 = l_Lean_indentExpr(x_12);
x_80 = l_Lean_Elab_Term_elabSubst___closed__8;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_Term_elabSubst___closed__10;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_indentExpr(x_44);
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
return x_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_44);
lean_dec(x_12);
x_93 = lean_box(0);
x_94 = l_Lean_Elab_Term_elabSubst___lambda__5(x_73, x_76, x_63, x_64, x_38, x_93, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_73);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_75);
if (x_95 == 0)
{
return x_75;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_75, 0);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_75);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_73);
lean_dec(x_44);
lean_dec(x_12);
x_99 = lean_box(0);
x_100 = l_Lean_Elab_Term_elabSubst___lambda__4(x_67, x_62, x_34, x_35, x_63, x_64, x_38, x_71, x_99, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
lean_dec(x_63);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_70);
if (x_101 == 0)
{
return x_70;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_70, 0);
x_103 = lean_ctor_get(x_70, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_70);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_46);
if (x_105 == 0)
{
return x_46;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_46, 0);
x_107 = lean_ctor_get(x_46, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_46);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_43);
if (x_109 == 0)
{
return x_43;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_43, 0);
x_111 = lean_ctor_get(x_43, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_43);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_40);
if (x_113 == 0)
{
return x_40;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_40, 0);
x_115 = lean_ctor_get(x_40, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_40);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_37);
if (x_117 == 0)
{
return x_37;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_37, 0);
x_119 = lean_ctor_get(x_37, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_37);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_11);
if (x_121 == 0)
{
return x_11;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_11, 0);
x_123 = lean_ctor_get(x_11, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_11);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabSubst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_elabSubst___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_elabSubst___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_2);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_elabSubst___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_5);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_elabSubst___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabSubst___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_mkArrow___at_Lean_Elab_Term_elabStateRefT___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_11 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_10, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = 0;
x_15 = l_Lean_mkForall(x_13, x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = 0;
x_19 = l_Lean_mkForall(x_16, x_18, x_1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelOne;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("STWorld");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("StateRefT'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
x_12 = l_Lean_Meta_mkArrow___at_Lean_Elab_Term_elabStateRefT___spec__1(x_11, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2;
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_elabTerm(x_2, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3;
x_22 = 0;
x_23 = lean_box(0);
lean_inc(x_6);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_23, x_6, x_7, x_8, x_9, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_mkAppStx___closed__9;
lean_inc(x_25);
x_28 = lean_array_push(x_27, x_25);
lean_inc(x_19);
x_29 = lean_array_push(x_28, x_19);
x_30 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isMonad_x3f___spec__1(x_30, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Elab_Term_mkInstMVar(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___closed__3;
x_37 = lean_array_push(x_36, x_25);
x_38 = lean_array_push(x_37, x_1);
x_39 = lean_array_push(x_38, x_19);
x_40 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isMonad_x3f___spec__1(x_40, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_apply_8(x_15, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_18);
if (x_57 == 0)
{
return x_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_18, 0);
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_18);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macroDollarArg");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_elabStateRefT___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_elabType(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_inc(x_16);
x_17 = l_Lean_Syntax_getKind(x_16);
x_18 = l_Lean_Elab_Term_elabStateRefT___closed__2;
x_19 = lean_name_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_elabStateRefT___lambda__2(x_13, x_16, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Syntax_getArg(x_16, x_10);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Term_elabStateRefT___lambda__2(x_13, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_mkArrow___at_Lean_Elab_Term_elabStateRefT___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkArrow___at_Lean_Elab_Term_elabStateRefT___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabStateRefT___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabStateRefT___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabStateRefT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stateRefT");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStateRefT___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_BuiltinNotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_BorrowedAnnotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandDollar___closed__1 = _init_l_Lean_Elab_Term_expandDollar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandDollar___closed__1);
l_Lean_Elab_Term_expandDollar___closed__2 = _init_l_Lean_Elab_Term_expandDollar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandDollar___closed__2);
l___regBuiltin_Lean_Elab_Term_expandDollar___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandDollar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDollar___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandDollar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandIf___closed__1 = _init_l_Lean_Elab_Term_expandIf___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__1);
l_Lean_Elab_Term_expandIf___closed__2 = _init_l_Lean_Elab_Term_expandIf___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__2);
l_Lean_Elab_Term_expandIf___closed__3 = _init_l_Lean_Elab_Term_expandIf___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__3);
l_Lean_Elab_Term_expandIf___closed__4 = _init_l_Lean_Elab_Term_expandIf___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__4);
l_Lean_Elab_Term_expandIf___closed__5 = _init_l_Lean_Elab_Term_expandIf___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__5);
l_Lean_Elab_Term_expandIf___closed__6 = _init_l_Lean_Elab_Term_expandIf___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__6);
l_Lean_Elab_Term_expandIf___closed__7 = _init_l_Lean_Elab_Term_expandIf___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__7);
l_Lean_Elab_Term_expandIf___closed__8 = _init_l_Lean_Elab_Term_expandIf___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__8);
l_Lean_Elab_Term_expandIf___closed__9 = _init_l_Lean_Elab_Term_expandIf___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__9);
l_Lean_Elab_Term_expandIf___closed__10 = _init_l_Lean_Elab_Term_expandIf___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__10);
l_Lean_Elab_Term_expandIf___closed__11 = _init_l_Lean_Elab_Term_expandIf___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__11);
l_Lean_Elab_Term_expandIf___closed__12 = _init_l_Lean_Elab_Term_expandIf___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandIf___closed__12);
l___regBuiltin_Lean_Elab_Term_expandIf___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandIf___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandIf___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandIf(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSubtype___closed__1 = _init_l_Lean_Elab_Term_expandSubtype___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__1);
l_Lean_Elab_Term_expandSubtype___closed__2 = _init_l_Lean_Elab_Term_expandSubtype___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__2);
l_Lean_Elab_Term_expandSubtype___closed__3 = _init_l_Lean_Elab_Term_expandSubtype___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__3);
l_Lean_Elab_Term_expandSubtype___closed__4 = _init_l_Lean_Elab_Term_expandSubtype___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__4);
l_Lean_Elab_Term_expandSubtype___closed__5 = _init_l_Lean_Elab_Term_expandSubtype___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__5);
l_Lean_Elab_Term_expandSubtype___closed__6 = _init_l_Lean_Elab_Term_expandSubtype___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__6);
l_Lean_Elab_Term_expandSubtype___closed__7 = _init_l_Lean_Elab_Term_expandSubtype___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__7);
l_Lean_Elab_Term_expandSubtype___closed__8 = _init_l_Lean_Elab_Term_expandSubtype___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__8);
l_Lean_Elab_Term_expandSubtype___closed__9 = _init_l_Lean_Elab_Term_expandSubtype___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__9);
l_Lean_Elab_Term_expandSubtype___closed__10 = _init_l_Lean_Elab_Term_expandSubtype___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__10);
l_Lean_Elab_Term_expandSubtype___closed__11 = _init_l_Lean_Elab_Term_expandSubtype___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__11);
l_Lean_Elab_Term_expandSubtype___closed__12 = _init_l_Lean_Elab_Term_expandSubtype___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandSubtype___closed__12);
l___regBuiltin_Lean_Elab_Term_expandSubtype___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSubtype___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSubtype___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandSubtype(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabAnonymousCtor___closed__1 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__1);
l_Lean_Elab_Term_elabAnonymousCtor___closed__2 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__2);
l_Lean_Elab_Term_elabAnonymousCtor___closed__3 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__3);
l_Lean_Elab_Term_elabAnonymousCtor___closed__4 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__4);
l_Lean_Elab_Term_elabAnonymousCtor___closed__5 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__5);
l_Lean_Elab_Term_elabAnonymousCtor___closed__6 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__6);
l_Lean_Elab_Term_elabAnonymousCtor___closed__7 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__7);
l_Lean_Elab_Term_elabAnonymousCtor___closed__8 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__8);
l_Lean_Elab_Term_elabAnonymousCtor___closed__9 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__9);
l_Lean_Elab_Term_elabAnonymousCtor___closed__10 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__10);
l_Lean_Elab_Term_elabAnonymousCtor___closed__11 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__11);
l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabBorrowed___closed__1 = _init_l_Lean_Elab_Term_elabBorrowed___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabBorrowed___closed__1);
l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandShow___closed__1 = _init_l_Lean_Elab_Term_expandShow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__1);
l_Lean_Elab_Term_expandShow___closed__2 = _init_l_Lean_Elab_Term_expandShow___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__2);
l_Lean_Elab_Term_expandShow___closed__3 = _init_l_Lean_Elab_Term_expandShow___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__3);
l_Lean_Elab_Term_expandShow___closed__4 = _init_l_Lean_Elab_Term_expandShow___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__4);
l_Lean_Elab_Term_expandShow___closed__5 = _init_l_Lean_Elab_Term_expandShow___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__5);
l_Lean_Elab_Term_expandShow___closed__6 = _init_l_Lean_Elab_Term_expandShow___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__6);
l_Lean_Elab_Term_expandShow___closed__7 = _init_l_Lean_Elab_Term_expandShow___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__7);
l_Lean_Elab_Term_expandShow___closed__8 = _init_l_Lean_Elab_Term_expandShow___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__8);
l_Lean_Elab_Term_expandShow___closed__9 = _init_l_Lean_Elab_Term_expandShow___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__9);
l_Lean_Elab_Term_expandShow___closed__10 = _init_l_Lean_Elab_Term_expandShow___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__10);
l_Lean_Elab_Term_expandShow___closed__11 = _init_l_Lean_Elab_Term_expandShow___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__11);
l_Lean_Elab_Term_expandShow___closed__12 = _init_l_Lean_Elab_Term_expandShow___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__12);
l_Lean_Elab_Term_expandShow___closed__13 = _init_l_Lean_Elab_Term_expandShow___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__13);
l_Lean_Elab_Term_expandShow___closed__14 = _init_l_Lean_Elab_Term_expandShow___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__14);
l_Lean_Elab_Term_expandShow___closed__15 = _init_l_Lean_Elab_Term_expandShow___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__15);
l_Lean_Elab_Term_expandShow___closed__16 = _init_l_Lean_Elab_Term_expandShow___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__16);
l___regBuiltin_Lean_Elab_Term_expandShow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandShow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandShow___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandShow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandHave___closed__1 = _init_l_Lean_Elab_Term_expandHave___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___closed__1);
l_Lean_Elab_Term_expandHave___closed__2 = _init_l_Lean_Elab_Term_expandHave___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___closed__2);
l___regBuiltin_Lean_Elab_Term_expandHave___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandHave___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandHave___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandHave(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSuffices___closed__1 = _init_l_Lean_Elab_Term_expandSuffices___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSuffices___closed__1);
l_Lean_Elab_Term_expandSuffices___closed__2 = _init_l_Lean_Elab_Term_expandSuffices___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSuffices___closed__2);
l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34);
l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1);
l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2);
l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__3);
l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4 = _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__4);
l_Lean_Elab_Term_elabParserMacro___closed__1 = _init_l_Lean_Elab_Term_elabParserMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___closed__1);
l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabParserMacro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10);
l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__1);
l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabTParserMacro___lambda__1___closed__2);
l_Lean_Elab_Term_elabTParserMacro___closed__1 = _init_l_Lean_Elab_Term_elabTParserMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTParserMacro___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabTParserMacro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8);
l_Lean_Elab_Term_elabNativeRefl___closed__1 = _init_l_Lean_Elab_Term_elabNativeRefl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___closed__1);
l_Lean_Elab_Term_elabNativeRefl___closed__2 = _init_l_Lean_Elab_Term_elabNativeRefl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabNativeRefl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5);
l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1 = _init_l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1);
l_Lean_Elab_Term_elabNativeDecide___rarg___closed__2 = _init_l_Lean_Elab_Term_elabNativeDecide___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeDecide___rarg___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabNativeDecide(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabDecide___rarg___closed__1 = _init_l_Lean_Elab_Term_elabDecide___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDecide___rarg___closed__1);
l_Lean_Elab_Term_elabDecide___rarg___closed__2 = _init_l_Lean_Elab_Term_elabDecide___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabDecide___rarg___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabDecide(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandProd___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandProd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandProd___closed__1);
l___regBuiltin_Lean_Elab_Term_expandProd___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandProd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandProd___closed__2);
l___regBuiltin_Lean_Elab_Term_expandProd___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandProd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandProd___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandProd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_ExpandFComp___closed__1 = _init_l_Lean_Elab_Term_ExpandFComp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ExpandFComp___closed__1);
l_Lean_Elab_Term_ExpandFComp___closed__2 = _init_l_Lean_Elab_Term_ExpandFComp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ExpandFComp___closed__2);
l_Lean_Elab_Term_ExpandFComp___closed__3 = _init_l_Lean_Elab_Term_ExpandFComp___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ExpandFComp___closed__3);
l_Lean_Elab_Term_ExpandFComp___closed__4 = _init_l_Lean_Elab_Term_ExpandFComp___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_ExpandFComp___closed__4);
l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__1);
l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__2);
l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_ExpandFComp___closed__3);
res = l___regBuiltin_Lean_Elab_Term_ExpandFComp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandAdd___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAdd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAdd___closed__1);
l___regBuiltin_Lean_Elab_Term_expandAdd___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandAdd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAdd___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandAdd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandSub___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSub___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSub___closed__1);
l___regBuiltin_Lean_Elab_Term_expandSub___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandSub___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSub___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandSub(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandMul___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandMul___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMul___closed__1);
l___regBuiltin_Lean_Elab_Term_expandMul___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandMul___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMul___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandMul(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandDiv___closed__1 = _init_l_Lean_Elab_Term_expandDiv___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandDiv___closed__1);
l_Lean_Elab_Term_expandDiv___closed__2 = _init_l_Lean_Elab_Term_expandDiv___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandDiv___closed__2);
l_Lean_Elab_Term_expandDiv___closed__3 = _init_l_Lean_Elab_Term_expandDiv___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandDiv___closed__3);
l___regBuiltin_Lean_Elab_Term_expandDiv___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandDiv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDiv___closed__1);
l___regBuiltin_Lean_Elab_Term_expandDiv___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandDiv___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDiv___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandDiv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandMod___closed__1 = _init_l_Lean_Elab_Term_expandMod___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMod___closed__1);
l_Lean_Elab_Term_expandMod___closed__2 = _init_l_Lean_Elab_Term_expandMod___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandMod___closed__2);
l_Lean_Elab_Term_expandMod___closed__3 = _init_l_Lean_Elab_Term_expandMod___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandMod___closed__3);
l___regBuiltin_Lean_Elab_Term_expandMod___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandMod___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMod___closed__1);
l___regBuiltin_Lean_Elab_Term_expandMod___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandMod___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMod___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandMod(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandModN___closed__1 = _init_l_Lean_Elab_Term_expandModN___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandModN___closed__1);
l_Lean_Elab_Term_expandModN___closed__2 = _init_l_Lean_Elab_Term_expandModN___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandModN___closed__2);
l_Lean_Elab_Term_expandModN___closed__3 = _init_l_Lean_Elab_Term_expandModN___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandModN___closed__3);
l_Lean_Elab_Term_expandModN___closed__4 = _init_l_Lean_Elab_Term_expandModN___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandModN___closed__4);
l___regBuiltin_Lean_Elab_Term_expandModN___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandModN___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandModN___closed__1);
l___regBuiltin_Lean_Elab_Term_expandModN___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandModN___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandModN___closed__2);
l___regBuiltin_Lean_Elab_Term_expandModN___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandModN___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandModN___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandModN(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandPow___closed__1 = _init_l_Lean_Elab_Term_expandPow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandPow___closed__1);
l_Lean_Elab_Term_expandPow___closed__2 = _init_l_Lean_Elab_Term_expandPow___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandPow___closed__2);
l_Lean_Elab_Term_expandPow___closed__3 = _init_l_Lean_Elab_Term_expandPow___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandPow___closed__3);
l_Lean_Elab_Term_expandPow___closed__4 = _init_l_Lean_Elab_Term_expandPow___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandPow___closed__4);
l___regBuiltin_Lean_Elab_Term_expandPow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandPow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandPow___closed__1);
l___regBuiltin_Lean_Elab_Term_expandPow___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandPow___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandPow___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandPow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandLE___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandLE___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandLE___closed__1);
l___regBuiltin_Lean_Elab_Term_expandLE___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandLE___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandLE___closed__2);
l___regBuiltin_Lean_Elab_Term_expandLE___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandLE___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandLE___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandLE(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandGE___closed__1 = _init_l_Lean_Elab_Term_expandGE___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandGE___closed__1);
l_Lean_Elab_Term_expandGE___closed__2 = _init_l_Lean_Elab_Term_expandGE___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandGE___closed__2);
l___regBuiltin_Lean_Elab_Term_expandGE___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandGE___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandGE___closed__1);
l___regBuiltin_Lean_Elab_Term_expandGE___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandGE___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandGE___closed__2);
l___regBuiltin_Lean_Elab_Term_expandGE___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandGE___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandGE___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandGE(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandLT___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandLT___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandLT___closed__1);
l___regBuiltin_Lean_Elab_Term_expandLT___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandLT___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandLT___closed__2);
l___regBuiltin_Lean_Elab_Term_expandLT___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandLT___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandLT___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandLT(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandGT___closed__1 = _init_l_Lean_Elab_Term_expandGT___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandGT___closed__1);
l_Lean_Elab_Term_expandGT___closed__2 = _init_l_Lean_Elab_Term_expandGT___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandGT___closed__2);
l___regBuiltin_Lean_Elab_Term_expandGT___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandGT___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandGT___closed__1);
l___regBuiltin_Lean_Elab_Term_expandGT___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandGT___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandGT___closed__2);
l___regBuiltin_Lean_Elab_Term_expandGT___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandGT___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandGT___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandGT(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandEq___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandEq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandEq___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandNe___closed__1 = _init_l_Lean_Elab_Term_expandNe___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandNe___closed__1);
l_Lean_Elab_Term_expandNe___closed__2 = _init_l_Lean_Elab_Term_expandNe___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandNe___closed__2);
l___regBuiltin_Lean_Elab_Term_expandNe___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandNe___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandNe___closed__1);
l___regBuiltin_Lean_Elab_Term_expandNe___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandNe___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandNe___closed__2);
l___regBuiltin_Lean_Elab_Term_expandNe___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandNe___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandNe___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandNe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandBEq___closed__1 = _init_l_Lean_Elab_Term_expandBEq___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandBEq___closed__1);
l_Lean_Elab_Term_expandBEq___closed__2 = _init_l_Lean_Elab_Term_expandBEq___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandBEq___closed__2);
l_Lean_Elab_Term_expandBEq___closed__3 = _init_l_Lean_Elab_Term_expandBEq___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandBEq___closed__3);
l___regBuiltin_Lean_Elab_Term_expandBEq___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandBEq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBEq___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandBEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandBNe___closed__1 = _init_l_Lean_Elab_Term_expandBNe___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandBNe___closed__1);
l_Lean_Elab_Term_expandBNe___closed__2 = _init_l_Lean_Elab_Term_expandBNe___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandBNe___closed__2);
l___regBuiltin_Lean_Elab_Term_expandBNe___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandBNe___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBNe___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBNe___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandBNe___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBNe___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandBNe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandHEq___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandHEq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandHEq___closed__1);
l___regBuiltin_Lean_Elab_Term_expandHEq___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandHEq___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandHEq___closed__2);
l___regBuiltin_Lean_Elab_Term_expandHEq___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandHEq___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandHEq___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandHEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandEquiv___closed__1 = _init_l_Lean_Elab_Term_expandEquiv___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandEquiv___closed__1);
l_Lean_Elab_Term_expandEquiv___closed__2 = _init_l_Lean_Elab_Term_expandEquiv___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandEquiv___closed__2);
l_Lean_Elab_Term_expandEquiv___closed__3 = _init_l_Lean_Elab_Term_expandEquiv___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandEquiv___closed__3);
l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__1);
l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__2);
l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandEquiv___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandEquiv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandAnd___closed__1 = _init_l_Lean_Elab_Term_expandAnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandAnd___closed__1);
l_Lean_Elab_Term_expandAnd___closed__2 = _init_l_Lean_Elab_Term_expandAnd___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandAnd___closed__2);
l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAnd___closed__1);
l___regBuiltin_Lean_Elab_Term_expandAnd___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandAnd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAnd___closed__2);
l___regBuiltin_Lean_Elab_Term_expandAnd___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandAnd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAnd___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandAnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandOr___closed__1 = _init_l_Lean_Elab_Term_expandOr___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandOr___closed__1);
l_Lean_Elab_Term_expandOr___closed__2 = _init_l_Lean_Elab_Term_expandOr___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandOr___closed__2);
l___regBuiltin_Lean_Elab_Term_expandOr___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandOr___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOr___closed__1);
l___regBuiltin_Lean_Elab_Term_expandOr___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandOr___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOr___closed__2);
l___regBuiltin_Lean_Elab_Term_expandOr___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandOr___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOr___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandOr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandIff___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandIff___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandIff___closed__1);
l___regBuiltin_Lean_Elab_Term_expandIff___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandIff___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandIff___closed__2);
l___regBuiltin_Lean_Elab_Term_expandIff___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandIff___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandIff___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandIff(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandBAnd___closed__1 = _init_l_Lean_Elab_Term_expandBAnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandBAnd___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBAnd___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandBAnd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBAnd___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandBAnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandBOr___closed__1 = _init_l_Lean_Elab_Term_expandBOr___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandBOr___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBOr___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandBOr___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBOr___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBOr___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandBOr___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBOr___closed__2);
l___regBuiltin_Lean_Elab_Term_expandBOr___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandBOr___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBOr___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandBOr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandAppend___closed__1 = _init_l_Lean_Elab_Term_expandAppend___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandAppend___closed__1);
l_Lean_Elab_Term_expandAppend___closed__2 = _init_l_Lean_Elab_Term_expandAppend___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandAppend___closed__2);
l_Lean_Elab_Term_expandAppend___closed__3 = _init_l_Lean_Elab_Term_expandAppend___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandAppend___closed__3);
l___regBuiltin_Lean_Elab_Term_expandAppend___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAppend___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAppend___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandAppend(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandCons___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandCons___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandCons___closed__1);
l___regBuiltin_Lean_Elab_Term_expandCons___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandCons___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandCons___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandCons(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandAndThen___closed__1 = _init_l_Lean_Elab_Term_expandAndThen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandAndThen___closed__1);
l_Lean_Elab_Term_expandAndThen___closed__2 = _init_l_Lean_Elab_Term_expandAndThen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandAndThen___closed__2);
l_Lean_Elab_Term_expandAndThen___closed__3 = _init_l_Lean_Elab_Term_expandAndThen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandAndThen___closed__3);
l_Lean_Elab_Term_expandAndThen___closed__4 = _init_l_Lean_Elab_Term_expandAndThen___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandAndThen___closed__4);
l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__1);
l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__2);
l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAndThen___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandAndThen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandBind___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandBind___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBind___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBind___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandBind___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBind___closed__2);
l___regBuiltin_Lean_Elab_Term_expandBind___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandBind___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBind___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandBind(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSeq___closed__1 = _init_l_Lean_Elab_Term_expandSeq___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSeq___closed__1);
l_Lean_Elab_Term_expandSeq___closed__2 = _init_l_Lean_Elab_Term_expandSeq___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSeq___closed__2);
l_Lean_Elab_Term_expandSeq___closed__3 = _init_l_Lean_Elab_Term_expandSeq___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSeq___closed__3);
l_Lean_Elab_Term_expandSeq___closed__4 = _init_l_Lean_Elab_Term_expandSeq___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSeq___closed__4);
l___regBuiltin_Lean_Elab_Term_expandSeq___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSeq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSeq___closed__1);
l___regBuiltin_Lean_Elab_Term_expandSeq___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandSeq___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSeq___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSeqLeft___closed__1 = _init_l_Lean_Elab_Term_expandSeqLeft___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqLeft___closed__1);
l_Lean_Elab_Term_expandSeqLeft___closed__2 = _init_l_Lean_Elab_Term_expandSeqLeft___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqLeft___closed__2);
l_Lean_Elab_Term_expandSeqLeft___closed__3 = _init_l_Lean_Elab_Term_expandSeqLeft___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqLeft___closed__3);
l_Lean_Elab_Term_expandSeqLeft___closed__4 = _init_l_Lean_Elab_Term_expandSeqLeft___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqLeft___closed__4);
l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__1);
l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSeqLeft___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandSeqLeft(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSeqRight___closed__1 = _init_l_Lean_Elab_Term_expandSeqRight___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqRight___closed__1);
l_Lean_Elab_Term_expandSeqRight___closed__2 = _init_l_Lean_Elab_Term_expandSeqRight___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqRight___closed__2);
l_Lean_Elab_Term_expandSeqRight___closed__3 = _init_l_Lean_Elab_Term_expandSeqRight___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqRight___closed__3);
l_Lean_Elab_Term_expandSeqRight___closed__4 = _init_l_Lean_Elab_Term_expandSeqRight___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSeqRight___closed__4);
l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__1);
l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSeqRight___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandSeqRight(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandMap___closed__1 = _init_l_Lean_Elab_Term_expandMap___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMap___closed__1);
l_Lean_Elab_Term_expandMap___closed__2 = _init_l_Lean_Elab_Term_expandMap___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandMap___closed__2);
l_Lean_Elab_Term_expandMap___closed__3 = _init_l_Lean_Elab_Term_expandMap___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandMap___closed__3);
l_Lean_Elab_Term_expandMap___closed__4 = _init_l_Lean_Elab_Term_expandMap___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandMap___closed__4);
l___regBuiltin_Lean_Elab_Term_expandMap___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandMap___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMap___closed__1);
l___regBuiltin_Lean_Elab_Term_expandMap___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandMap___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMap___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandMapRev___closed__1 = _init_l_Lean_Elab_Term_expandMapRev___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMapRev___closed__1);
l_Lean_Elab_Term_expandMapRev___closed__2 = _init_l_Lean_Elab_Term_expandMapRev___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandMapRev___closed__2);
l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__1);
l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandMapRev___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandMapRev(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__1);
l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOrElse___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandOrElse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandOrM___closed__1 = _init_l_Lean_Elab_Term_expandOrM___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandOrM___closed__1);
l_Lean_Elab_Term_expandOrM___closed__2 = _init_l_Lean_Elab_Term_expandOrM___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandOrM___closed__2);
l___regBuiltin_Lean_Elab_Term_expandOrM___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandOrM___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOrM___closed__1);
l___regBuiltin_Lean_Elab_Term_expandOrM___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandOrM___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandOrM___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandOrM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandAndM___closed__1 = _init_l_Lean_Elab_Term_expandAndM___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandAndM___closed__1);
l_Lean_Elab_Term_expandAndM___closed__2 = _init_l_Lean_Elab_Term_expandAndM___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandAndM___closed__2);
l___regBuiltin_Lean_Elab_Term_expandAndM___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAndM___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAndM___closed__1);
l___regBuiltin_Lean_Elab_Term_expandAndM___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandAndM___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAndM___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandAndM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandNot___closed__1 = _init_l_Lean_Elab_Term_expandNot___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandNot___closed__1);
l_Lean_Elab_Term_expandNot___closed__2 = _init_l_Lean_Elab_Term_expandNot___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandNot___closed__2);
l___regBuiltin_Lean_Elab_Term_expandNot___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandNot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandNot___closed__1);
l___regBuiltin_Lean_Elab_Term_expandNot___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandNot___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandNot___closed__2);
l___regBuiltin_Lean_Elab_Term_expandNot___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandNot___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandNot___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandNot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandBNot___closed__1 = _init_l_Lean_Elab_Term_expandBNot___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandBNot___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBNot___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandBNot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBNot___closed__1);
l___regBuiltin_Lean_Elab_Term_expandBNot___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandBNot___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBNot___closed__2);
l___regBuiltin_Lean_Elab_Term_expandBNot___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandBNot___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandBNot___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandBNot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandUMinus___closed__1 = _init_l_Lean_Elab_Term_expandUMinus___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandUMinus___closed__1);
l_Lean_Elab_Term_expandUMinus___closed__2 = _init_l_Lean_Elab_Term_expandUMinus___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandUMinus___closed__2);
l_Lean_Elab_Term_expandUMinus___closed__3 = _init_l_Lean_Elab_Term_expandUMinus___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandUMinus___closed__3);
l_Lean_Elab_Term_expandUMinus___closed__4 = _init_l_Lean_Elab_Term_expandUMinus___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandUMinus___closed__4);
l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__1);
l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__2);
l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUMinus___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandUMinus(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabPanic___closed__1 = _init_l_Lean_Elab_Term_elabPanic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__1);
l_Lean_Elab_Term_elabPanic___closed__2 = _init_l_Lean_Elab_Term_elabPanic___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__2);
l_Lean_Elab_Term_elabPanic___closed__3 = _init_l_Lean_Elab_Term_elabPanic___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__3);
l_Lean_Elab_Term_elabPanic___closed__4 = _init_l_Lean_Elab_Term_elabPanic___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__4);
l_Lean_Elab_Term_elabPanic___closed__5 = _init_l_Lean_Elab_Term_elabPanic___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__5);
l_Lean_Elab_Term_elabPanic___closed__6 = _init_l_Lean_Elab_Term_elabPanic___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__6);
l_Lean_Elab_Term_elabPanic___closed__7 = _init_l_Lean_Elab_Term_elabPanic___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__7);
l_Lean_Elab_Term_elabPanic___closed__8 = _init_l_Lean_Elab_Term_elabPanic___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__8);
l_Lean_Elab_Term_elabPanic___closed__9 = _init_l_Lean_Elab_Term_elabPanic___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__9);
l_Lean_Elab_Term_elabPanic___closed__10 = _init_l_Lean_Elab_Term_elabPanic___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__10);
l_Lean_Elab_Term_elabPanic___closed__11 = _init_l_Lean_Elab_Term_elabPanic___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__11);
l_Lean_Elab_Term_elabPanic___closed__12 = _init_l_Lean_Elab_Term_elabPanic___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__12);
l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1);
l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPanic___closed__2);
l___regBuiltin_Lean_Elab_Term_elabPanic___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPanic___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabPanic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__1 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__1);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__2 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__2);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__3 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__3);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__4 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__4);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__5 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__5);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__6 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__6);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__7 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__7);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__8 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__8);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__9 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__9);
l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1);
l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__2);
l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandAssert___closed__1 = _init_l_Lean_Elab_Term_expandAssert___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__1);
l_Lean_Elab_Term_expandAssert___closed__2 = _init_l_Lean_Elab_Term_expandAssert___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__2);
l_Lean_Elab_Term_expandAssert___closed__3 = _init_l_Lean_Elab_Term_expandAssert___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__3);
l_Lean_Elab_Term_expandAssert___closed__4 = _init_l_Lean_Elab_Term_expandAssert___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__4);
l_Lean_Elab_Term_expandAssert___closed__5 = _init_l_Lean_Elab_Term_expandAssert___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__5);
l_Lean_Elab_Term_expandAssert___closed__6 = _init_l_Lean_Elab_Term_expandAssert___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__6);
l_Lean_Elab_Term_expandAssert___closed__7 = _init_l_Lean_Elab_Term_expandAssert___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__7);
l_Lean_Elab_Term_expandAssert___closed__8 = _init_l_Lean_Elab_Term_expandAssert___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__8);
l_Lean_Elab_Term_expandAssert___closed__9 = _init_l_Lean_Elab_Term_expandAssert___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__9);
l_Lean_Elab_Term_expandAssert___closed__10 = _init_l_Lean_Elab_Term_expandAssert___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__10);
l_Lean_Elab_Term_expandAssert___closed__11 = _init_l_Lean_Elab_Term_expandAssert___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__11);
l_Lean_Elab_Term_expandAssert___closed__12 = _init_l_Lean_Elab_Term_expandAssert___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__12);
l_Lean_Elab_Term_expandAssert___closed__13 = _init_l_Lean_Elab_Term_expandAssert___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__13);
l_Lean_Elab_Term_expandAssert___closed__14 = _init_l_Lean_Elab_Term_expandAssert___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__14);
l_Lean_Elab_Term_expandAssert___closed__15 = _init_l_Lean_Elab_Term_expandAssert___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__15);
l_Lean_Elab_Term_expandAssert___closed__16 = _init_l_Lean_Elab_Term_expandAssert___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__16);
l_Lean_Elab_Term_expandAssert___closed__17 = _init_l_Lean_Elab_Term_expandAssert___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__17);
l_Lean_Elab_Term_expandAssert___closed__18 = _init_l_Lean_Elab_Term_expandAssert___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__18);
l_Lean_Elab_Term_expandAssert___closed__19 = _init_l_Lean_Elab_Term_expandAssert___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__19);
l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1);
l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2);
l___regBuiltin_Lean_Elab_Term_expandAssert___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAssert___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandAssert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandDbgTrace___closed__1 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__1);
l_Lean_Elab_Term_expandDbgTrace___closed__2 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__2);
l_Lean_Elab_Term_expandDbgTrace___closed__3 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__3);
l_Lean_Elab_Term_expandDbgTrace___closed__4 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__4);
l_Lean_Elab_Term_expandDbgTrace___closed__5 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__5);
l_Lean_Elab_Term_expandDbgTrace___closed__6 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__6);
l_Lean_Elab_Term_expandDbgTrace___closed__7 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__7);
l_Lean_Elab_Term_expandDbgTrace___closed__8 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__8);
l_Lean_Elab_Term_expandDbgTrace___closed__9 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__9);
l_Lean_Elab_Term_expandDbgTrace___closed__10 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__10);
l_Lean_Elab_Term_expandDbgTrace___closed__11 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__11);
l_Lean_Elab_Term_expandDbgTrace___closed__12 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__12);
l_Lean_Elab_Term_expandDbgTrace___closed__13 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__13);
l_Lean_Elab_Term_expandDbgTrace___closed__14 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__14);
l_Lean_Elab_Term_expandDbgTrace___closed__15 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__15);
l_Lean_Elab_Term_expandDbgTrace___closed__16 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__16);
l_Lean_Elab_Term_expandDbgTrace___closed__17 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__17);
l_Lean_Elab_Term_expandDbgTrace___closed__18 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__18);
l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1);
l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__2);
res = l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSorry___rarg___closed__1 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__1);
l_Lean_Elab_Term_expandSorry___rarg___closed__2 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__2);
l_Lean_Elab_Term_expandSorry___rarg___closed__3 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__3);
l_Lean_Elab_Term_expandSorry___rarg___closed__4 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__4);
l_Lean_Elab_Term_expandSorry___rarg___closed__5 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__5);
l_Lean_Elab_Term_expandSorry___rarg___closed__6 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__6);
l_Lean_Elab_Term_expandSorry___rarg___closed__7 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__7);
l_Lean_Elab_Term_expandSorry___rarg___closed__8 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__8);
l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandSorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandEmptyC___closed__1 = _init_l_Lean_Elab_Term_expandEmptyC___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__1);
l_Lean_Elab_Term_expandEmptyC___closed__2 = _init_l_Lean_Elab_Term_expandEmptyC___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__2);
l_Lean_Elab_Term_expandEmptyC___closed__3 = _init_l_Lean_Elab_Term_expandEmptyC___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__3);
l_Lean_Elab_Term_expandEmptyC___closed__4 = _init_l_Lean_Elab_Term_expandEmptyC___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__4);
l_Lean_Elab_Term_expandEmptyC___closed__5 = _init_l_Lean_Elab_Term_expandEmptyC___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__5);
l_Lean_Elab_Term_expandEmptyC___closed__6 = _init_l_Lean_Elab_Term_expandEmptyC___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__6);
l_Lean_Elab_Term_expandEmptyC___closed__7 = _init_l_Lean_Elab_Term_expandEmptyC___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__7);
l_Lean_Elab_Term_expandEmptyC___closed__8 = _init_l_Lean_Elab_Term_expandEmptyC___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__8);
l_Lean_Elab_Term_expandEmptyC___closed__9 = _init_l_Lean_Elab_Term_expandEmptyC___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__9);
l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkPairs_loop___closed__1 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__1);
l_Lean_Elab_Term_mkPairs_loop___closed__2 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__2);
l_Lean_Elab_Term_mkPairs_loop___closed__3 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__3);
l_Lean_Elab_Term_mkPairs_loop___closed__4 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__4);
l_Lean_Elab_Term_mkPairs_loop___closed__5 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__5);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1);
l_Lean_Elab_Term_elabParen___closed__1 = _init_l_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__1);
l_Lean_Elab_Term_elabParen___closed__2 = _init_l_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__2);
l_Lean_Elab_Term_elabParen___closed__3 = _init_l_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__3);
l_Lean_Elab_Term_elabParen___closed__4 = _init_l_Lean_Elab_Term_elabParen___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__4);
l_Lean_Elab_Term_elabParen___closed__5 = _init_l_Lean_Elab_Term_elabParen___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__5);
l___regBuiltin_Lean_Elab_Term_elabParen___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabParen___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabSubst___closed__1 = _init_l_Lean_Elab_Term_elabSubst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__1);
l_Lean_Elab_Term_elabSubst___closed__2 = _init_l_Lean_Elab_Term_elabSubst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__2);
l_Lean_Elab_Term_elabSubst___closed__3 = _init_l_Lean_Elab_Term_elabSubst___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__3);
l_Lean_Elab_Term_elabSubst___closed__4 = _init_l_Lean_Elab_Term_elabSubst___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__4);
l_Lean_Elab_Term_elabSubst___closed__5 = _init_l_Lean_Elab_Term_elabSubst___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__5);
l_Lean_Elab_Term_elabSubst___closed__6 = _init_l_Lean_Elab_Term_elabSubst___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__6);
l_Lean_Elab_Term_elabSubst___closed__7 = _init_l_Lean_Elab_Term_elabSubst___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__7);
l_Lean_Elab_Term_elabSubst___closed__8 = _init_l_Lean_Elab_Term_elabSubst___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__8);
l_Lean_Elab_Term_elabSubst___closed__9 = _init_l_Lean_Elab_Term_elabSubst___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__9);
l_Lean_Elab_Term_elabSubst___closed__10 = _init_l_Lean_Elab_Term_elabSubst___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__10);
l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7);
l_Lean_Elab_Term_elabStateRefT___closed__1 = _init_l_Lean_Elab_Term_elabStateRefT___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___closed__1);
l_Lean_Elab_Term_elabStateRefT___closed__2 = _init_l_Lean_Elab_Term_elabStateRefT___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___closed__2);
l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1);
l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__2);
l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
