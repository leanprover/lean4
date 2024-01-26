// Lean compiler output
// Module: Lean.Elab.Tactic.Simproc
// Imports: Init Lean.Meta.Tactic.Simp.Simproc Lean.Elab.Binders Lean.Elab.SyntheticMVars Lean.Elab.Term Lean.Elab.Command
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__8;
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabSimprocPattern___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__6;
lean_object* l_List_mapTR_loop___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__24;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__4;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__12;
static lean_object* l_Lean_Elab_checkSimprocType___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26;
lean_object* l_Lean_Expr_lit___override(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__3;
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__4;
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__13;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__7;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__5;
static lean_object* l_Lean_Elab_checkSimprocType___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__10;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__10;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__1;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__6;
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__20;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__9;
lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__18;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__4;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__4;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__5;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__17;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11;
lean_object* l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__7;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8;
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5;
static lean_object* l_Lean_Elab_checkSimprocType___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__13;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__3;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
extern lean_object* l_Lean_Meta_simpDtConfig;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__3;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__8;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lambda__2___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__7;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2;
lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__18;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabSimprocPattern___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__6;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__2;
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__19;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__4;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__4;
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__7;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__6;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__5;
static lean_object* l_Lean_Elab_checkSimprocType___closed__4;
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__15;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__7;
lean_object* l_Lean_throwError___at_Lean_declareBuiltin___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__16;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7;
static lean_object* l_Lean_Elab_checkSimprocType___closed__5;
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__14;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__3;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__11;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__9;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__5;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__1;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__15;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__5;
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__2;
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__20;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747_(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4;
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lambda__2(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__16;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__1;
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20;
lean_object* l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__8;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__7;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__1;
static lean_object* l_Lean_Elab_checkSimprocType___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_10, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_12);
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
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSimprocPattern___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_elabSimprocPattern___closed__2;
x_3 = l_Lean_Elab_elabSimprocPattern___closed__1;
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
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 1;
x_5 = 0;
x_6 = l_Lean_Elab_elabSimprocPattern___closed__3;
x_7 = l_Lean_Elab_elabSimprocPattern___closed__4;
x_8 = lean_alloc_ctor(0, 8, 9);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
lean_ctor_set(x_8, 5, x_2);
lean_ctor_set(x_8, 6, x_2);
lean_ctor_set(x_8, 7, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 3, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 4, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 5, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 7, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 8, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lambda__1), 9, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_elabSimprocPattern___closed__5;
x_10 = l_Lean_Elab_elabSimprocPattern___closed__6;
x_11 = l_Lean_Elab_Term_TermElabM_run___rarg(x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_elabSimprocPattern___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Elab_elabSimprocPattern(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_simpDtConfig;
x_11 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected type at '", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSimprocType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', 'Simproc' expected", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSimprocType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Simproc", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_Elab_checkSimprocType___closed__5;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_5);
x_21 = l_Lean_MessageData_ofName(x_1);
x_22 = l_Lean_Elab_checkSimprocType___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_checkSimprocType___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_25, x_2, x_3, x_8);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Elab_checkSimprocType___closed__6;
x_28 = lean_string_dec_eq(x_17, x_27);
lean_dec(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_5);
x_29 = l_Lean_MessageData_ofName(x_1);
x_30 = l_Lean_Elab_checkSimprocType___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_checkSimprocType___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_33, x_2, x_3, x_8);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Elab_checkSimprocType___closed__7;
x_36 = lean_string_dec_eq(x_16, x_35);
lean_dec(x_16);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
lean_free_object(x_5);
x_37 = l_Lean_MessageData_ofName(x_1);
x_38 = l_Lean_Elab_checkSimprocType___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_checkSimprocType___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_41, x_2, x_3, x_8);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Elab_checkSimprocType___closed__8;
x_44 = lean_string_dec_eq(x_15, x_43);
lean_dec(x_15);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_5);
x_45 = l_Lean_MessageData_ofName(x_1);
x_46 = l_Lean_Elab_checkSimprocType___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_checkSimprocType___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_49, x_2, x_3, x_8);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_5, 0, x_51);
return x_5;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_52 = l_Lean_MessageData_ofName(x_1);
x_53 = l_Lean_Elab_checkSimprocType___closed__2;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_checkSimprocType___closed__4;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_56, x_2, x_3, x_8);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_58 = l_Lean_MessageData_ofName(x_1);
x_59 = l_Lean_Elab_checkSimprocType___closed__2;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Elab_checkSimprocType___closed__4;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_62, x_2, x_3, x_8);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_64 = l_Lean_MessageData_ofName(x_1);
x_65 = l_Lean_Elab_checkSimprocType___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_checkSimprocType___closed__4;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_68, x_2, x_3, x_8);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_70 = l_Lean_MessageData_ofName(x_1);
x_71 = l_Lean_Elab_checkSimprocType___closed__2;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Elab_checkSimprocType___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_74, x_2, x_3, x_8);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_10);
lean_free_object(x_5);
x_76 = l_Lean_MessageData_ofName(x_1);
x_77 = l_Lean_Elab_checkSimprocType___closed__2;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_Elab_checkSimprocType___closed__4;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_80, x_2, x_3, x_8);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
lean_free_object(x_5);
x_82 = l_Lean_MessageData_ofName(x_1);
x_83 = l_Lean_Elab_checkSimprocType___closed__2;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Elab_checkSimprocType___closed__4;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_86, x_2, x_3, x_8);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
x_90 = l_Lean_ConstantInfo_type(x_88);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 4)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 1)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 1)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = l_Lean_Elab_checkSimprocType___closed__5;
x_101 = lean_string_dec_eq(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_102 = l_Lean_MessageData_ofName(x_1);
x_103 = l_Lean_Elab_checkSimprocType___closed__2;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Elab_checkSimprocType___closed__4;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_106, x_2, x_3, x_89);
return x_107;
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = l_Lean_Elab_checkSimprocType___closed__6;
x_109 = lean_string_dec_eq(x_98, x_108);
lean_dec(x_98);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_97);
lean_dec(x_96);
x_110 = l_Lean_MessageData_ofName(x_1);
x_111 = l_Lean_Elab_checkSimprocType___closed__2;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_Elab_checkSimprocType___closed__4;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_114, x_2, x_3, x_89);
return x_115;
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_Lean_Elab_checkSimprocType___closed__7;
x_117 = lean_string_dec_eq(x_97, x_116);
lean_dec(x_97);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_96);
x_118 = l_Lean_MessageData_ofName(x_1);
x_119 = l_Lean_Elab_checkSimprocType___closed__2;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_Elab_checkSimprocType___closed__4;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_122, x_2, x_3, x_89);
return x_123;
}
else
{
lean_object* x_124; uint8_t x_125; 
x_124 = l_Lean_Elab_checkSimprocType___closed__8;
x_125 = lean_string_dec_eq(x_96, x_124);
lean_dec(x_96);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = l_Lean_MessageData_ofName(x_1);
x_127 = l_Lean_Elab_checkSimprocType___closed__2;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Elab_checkSimprocType___closed__4;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_130, x_2, x_3, x_89);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_1);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_89);
return x_133;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
x_134 = l_Lean_MessageData_ofName(x_1);
x_135 = l_Lean_Elab_checkSimprocType___closed__2;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_Elab_checkSimprocType___closed__4;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_138, x_2, x_3, x_89);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
x_140 = l_Lean_MessageData_ofName(x_1);
x_141 = l_Lean_Elab_checkSimprocType___closed__2;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_Elab_checkSimprocType___closed__4;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_144, x_2, x_3, x_89);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
x_146 = l_Lean_MessageData_ofName(x_1);
x_147 = l_Lean_Elab_checkSimprocType___closed__2;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_Elab_checkSimprocType___closed__4;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_150, x_2, x_3, x_89);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_92);
lean_dec(x_91);
x_152 = l_Lean_MessageData_ofName(x_1);
x_153 = l_Lean_Elab_checkSimprocType___closed__2;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Elab_checkSimprocType___closed__4;
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_156, x_2, x_3, x_89);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_91);
x_158 = l_Lean_MessageData_ofName(x_1);
x_159 = l_Lean_Elab_checkSimprocType___closed__2;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Elab_checkSimprocType___closed__4;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_162, x_2, x_3, x_89);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_90);
x_164 = l_Lean_MessageData_ofName(x_1);
x_165 = l_Lean_Elab_checkSimprocType___closed__2;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Elab_checkSimprocType___closed__4;
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_168, x_2, x_3, x_89);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_5);
if (x_170 == 0)
{
return x_5;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_5, 0);
x_172 = lean_ctor_get(x_5, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_5);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSimprocType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__16(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__16(x_2, x_20, x_4, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabSimprocPattern___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_8, x_12, x_16, x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_ResolveName_resolveGlobalName(x_8, x_12, x_20, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_1, x_5);
x_7 = l_Lean_MessageData_ofExpr(x_6);
x_8 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__2;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabSimprocPattern___spec__6(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(x_6, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5___lambda__1(x_9, x_8, x_11, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7(x_1, x_2, x_3, x_7);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_6);
x_8 = l_List_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 6);
lean_dec(x_15);
lean_ctor_set(x_2, 6, x_13);
x_16 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5(x_5, x_2, x_3, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_24, 6, x_13);
lean_ctor_set(x_24, 7, x_23);
x_25 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5(x_5, x_24, x_3, x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__3;
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__4(x_1, x_26, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous identifier '", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux(x_8, x_9, x_10, x_1);
x_12 = l_Std_Format_defWidth;
x_13 = lean_format_pretty(x_11, x_12);
x_14 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_List_mapTR_loop___at_Lean_resolveGlobalConstNoOverload___spec__1(x_6, x_18);
x_20 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__8(x_1, x_25, x_2, x_3, x_7);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_38 = l_Lean_Syntax_formatStxAux(x_35, x_36, x_37, x_1);
x_39 = l_Std_Format_defWidth;
x_40 = lean_format_pretty(x_38, x_39);
x_41 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_box(0);
x_46 = l_List_mapTR_loop___at_Lean_resolveGlobalConstNoOverload___spec__1(x_6, x_45);
x_47 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_46);
lean_dec(x_46);
x_48 = lean_string_append(x_44, x_47);
lean_dec(x_47);
x_49 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__8(x_1, x_52, x_2, x_3, x_34);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
return x_5;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Elab_checkSimprocType(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Elab_elabSimprocKeys(x_2, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Simp_registerSimproc(x_1, x_13, x_7, x_8, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simprocPattern", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSimprocPattern___closed__3;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2(x_11, x_2, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___lambda__1___boxed), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_9);
x_16 = l_Lean_Elab_Command_liftTermElabM___rarg(x_15, x_2, x_3, x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSimprocPattern___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabSimprocPattern___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabSimprocPattern___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabSimprocPattern___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabSimprocPattern___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSimprocPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSimprocPattern", 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__1;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__2;
x_4 = lean_unsigned_to_nat(33u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__4;
x_2 = lean_unsigned_to_nat(55u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__5;
x_4 = lean_unsigned_to_nat(73u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("DiscrTree", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Key", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("const", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fvar", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FVarId", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lit", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Literal", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("natVal", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("strVal", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("star", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("other", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("arrow", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_2);
x_6 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(x_1, x_2, x_5);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_7);
x_10 = l_Lean_mkNatLit(x_8);
x_11 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5;
x_12 = l_Lean_mkAppB(x_11, x_9, x_10);
x_13 = l_Lean_mkAppB(x_2, x_12, x_6);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_14);
x_17 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12;
x_18 = l_Lean_Expr_app___override(x_17, x_16);
x_19 = l_Lean_mkNatLit(x_15);
x_20 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8;
x_21 = l_Lean_mkAppB(x_20, x_18, x_19);
x_22 = l_Lean_mkAppB(x_2, x_21, x_6);
return x_22;
}
case 2:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l_Lean_Expr_lit___override(x_23);
x_25 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19;
x_26 = l_Lean_Expr_app___override(x_25, x_24);
x_27 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15;
x_28 = l_Lean_Expr_app___override(x_27, x_26);
x_29 = l_Lean_mkAppB(x_2, x_28, x_6);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = l_Lean_Expr_lit___override(x_23);
x_31 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22;
x_32 = l_Lean_Expr_app___override(x_31, x_30);
x_33 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15;
x_34 = l_Lean_Expr_app___override(x_33, x_32);
x_35 = l_Lean_mkAppB(x_2, x_34, x_6);
return x_35;
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25;
x_37 = l_Lean_mkAppB(x_2, x_36, x_6);
return x_37;
}
case 4:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28;
x_39 = l_Lean_mkAppB(x_2, x_38, x_6);
return x_39;
}
case 5:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31;
x_41 = l_Lean_mkAppB(x_2, x_40, x_6);
return x_41;
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
lean_dec(x_4);
x_45 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_42);
x_46 = l_Lean_mkNatLit(x_43);
x_47 = l_Lean_mkNatLit(x_44);
x_48 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34;
x_49 = l_Lean_mkApp3(x_48, x_45, x_46, x_47);
x_50 = l_Lean_mkAppB(x_2, x_49, x_6);
return x_50;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("registerBuiltinSimproc", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l_Lean_Elab_checkSimprocType___closed__7;
x_4 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("List", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toArray", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nil", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cons", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declare", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Elab_checkSimprocType(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Elab_elabSimprocKeys(x_2, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_1);
x_16 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
x_17 = lean_array_to_list(lean_box(0), x_13);
x_18 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14;
x_19 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18;
x_20 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(x_18, x_19, x_17);
x_21 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10;
x_22 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5;
x_23 = l_Lean_mkAppB(x_21, x_22, x_20);
lean_inc(x_1);
x_24 = l_Lean_Expr_const___override(x_1, x_15);
x_25 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19;
x_26 = lean_array_push(x_25, x_16);
x_27 = lean_array_push(x_26, x_23);
x_28 = lean_array_push(x_27, x_24);
x_29 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3;
x_30 = l_Lean_mkAppN(x_29, x_28);
x_31 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21;
x_32 = l_Lean_Name_append(x_1, x_31);
x_33 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_32, x_7, x_8, x_14);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_declareBuiltin(x_34, x_30, x_7, x_8, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simprocPatternBuiltin", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2(x_11, x_2, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___boxed), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_9);
x_16 = l_Lean_Elab_Command_liftTermElabM___rarg(x_15, x_2, x_3, x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSimprocPatternBuiltin", 25);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5;
x_3 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__1;
x_2 = lean_unsigned_to_nat(58u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__2;
x_4 = lean_unsigned_to_nat(35u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(87u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__4;
x_2 = lean_unsigned_to_nat(62u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__5;
x_4 = lean_unsigned_to_nat(87u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__3;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__4;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__5;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__10;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__11;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__13;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__14;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__19;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__7;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__9;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__16;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__20;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__6;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__21;
x_4 = l_Lean_Elab_elabSimprocPattern___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpPost", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__24;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
x_10 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22;
x_11 = lean_st_mk_ref(x_10, x_6);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_8, x_14);
lean_dec(x_8);
x_16 = l_Lean_Syntax_getKind(x_15);
x_17 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25;
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_16);
x_19 = l_Lean_Meta_Simp_addSimprocAttr(x_1, x_3, x_18, x_4, x_5, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_12, x_21);
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
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
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_8);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = 1;
x_34 = l_Lean_Meta_Simp_addSimprocAttr(x_1, x_3, x_33, x_4, x_5, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_31, x_36);
lean_dec(x_31);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_31);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_checkSimprocType___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__2;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__4;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__6;
x_2 = l_Lean_Elab_checkSimprocType___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__7;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__8;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__9;
x_2 = l_Lean_Elab_checkSimprocType___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__10;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12;
x_2 = lean_unsigned_to_nat(568u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simprocAttr", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Simplification procedure", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__13;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__15;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__16;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__17;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__18;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__20;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("addSimprocBuiltinAttr", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l_Lean_Elab_checkSimprocType___closed__7;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_1, x_10);
x_13 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19;
x_14 = lean_array_push(x_13, x_11);
x_15 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21;
x_16 = l_Lean_Name_append(x_1, x_15);
x_17 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22;
x_18 = lean_st_mk_ref(x_17, x_6);
if (x_9 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_8, x_19);
lean_dec(x_8);
x_21 = l_Lean_Syntax_getKind(x_20);
x_22 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25;
x_23 = lean_name_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__7;
x_27 = lean_array_push(x_14, x_26);
x_28 = lean_array_push(x_27, x_12);
x_29 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3;
x_30 = l_Lean_mkAppN(x_29, x_28);
x_31 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_16, x_4, x_5, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_declareBuiltin(x_32, x_30, x_4, x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_24, x_36);
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_24);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10;
x_49 = lean_array_push(x_14, x_48);
x_50 = lean_array_push(x_49, x_12);
x_51 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3;
x_52 = l_Lean_mkAppN(x_51, x_50);
x_53 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_16, x_4, x_5, x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_declareBuiltin(x_54, x_52, x_4, x_5, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_46, x_58);
lean_dec(x_46);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_46);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
x_68 = lean_ctor_get(x_18, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_dec(x_18);
x_70 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10;
x_71 = lean_array_push(x_14, x_70);
x_72 = lean_array_push(x_71, x_12);
x_73 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3;
x_74 = l_Lean_mkAppN(x_73, x_72);
x_75 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_16, x_4, x_5, x_69);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_declareBuiltin(x_76, x_74, x_4, x_5, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_get(x_68, x_80);
lean_dec(x_68);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_68);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
return x_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_78);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12;
x_2 = lean_unsigned_to_nat(747u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simprocBuiltinAttr", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Builtin simplification procedure", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__3;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__4;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__5;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__6;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__7;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabSimprocPattern___closed__1 = _init_l_Lean_Elab_elabSimprocPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__1);
l_Lean_Elab_elabSimprocPattern___closed__2 = _init_l_Lean_Elab_elabSimprocPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__2);
l_Lean_Elab_elabSimprocPattern___closed__3 = _init_l_Lean_Elab_elabSimprocPattern___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__3);
l_Lean_Elab_elabSimprocPattern___closed__4 = _init_l_Lean_Elab_elabSimprocPattern___closed__4();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__4);
l_Lean_Elab_elabSimprocPattern___closed__5 = _init_l_Lean_Elab_elabSimprocPattern___closed__5();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__5);
l_Lean_Elab_elabSimprocPattern___closed__6 = _init_l_Lean_Elab_elabSimprocPattern___closed__6();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__6);
l_Lean_Elab_checkSimprocType___closed__1 = _init_l_Lean_Elab_checkSimprocType___closed__1();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__1);
l_Lean_Elab_checkSimprocType___closed__2 = _init_l_Lean_Elab_checkSimprocType___closed__2();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__2);
l_Lean_Elab_checkSimprocType___closed__3 = _init_l_Lean_Elab_checkSimprocType___closed__3();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__3);
l_Lean_Elab_checkSimprocType___closed__4 = _init_l_Lean_Elab_checkSimprocType___closed__4();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__4);
l_Lean_Elab_checkSimprocType___closed__5 = _init_l_Lean_Elab_checkSimprocType___closed__5();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__5);
l_Lean_Elab_checkSimprocType___closed__6 = _init_l_Lean_Elab_checkSimprocType___closed__6();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__6);
l_Lean_Elab_checkSimprocType___closed__7 = _init_l_Lean_Elab_checkSimprocType___closed__7();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__7);
l_Lean_Elab_checkSimprocType___closed__8 = _init_l_Lean_Elab_checkSimprocType___closed__8();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__8);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__3);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__4 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabSimprocPattern___spec__7___closed__4);
l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__1);
l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__2 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__2);
l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__3 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabSimprocPattern___spec__3___closed__3);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__1);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__2);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabSimprocPattern___spec__2___closed__3);
l_Lean_Elab_Command_elabSimprocPattern___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__1);
l_Lean_Elab_Command_elabSimprocPattern___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__2);
l_Lean_Elab_Command_elabSimprocPattern___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__16);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__17 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__17);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__18 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__18);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__19 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__19);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__20 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__20);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__21 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__21);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__22);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__23);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__24 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__24);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____lambda__1___closed__25);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__16);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__17 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__17();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__17);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__18 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__18();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__18);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__19);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__20 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__20();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568____closed__20);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_568_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____lambda__1___closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747____closed__7);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Tactic_Simproc___hyg_747_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
