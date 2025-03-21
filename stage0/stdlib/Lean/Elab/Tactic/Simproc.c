// Lean compiler output
// Module: Lean.Elab.Tactic.Simproc
// Imports: Init.Simproc Lean.ReservedNameAction Lean.Meta.Tactic.Simp.Simproc Lean.Elab.Binders Lean.Elab.SyntheticMVars Lean.Elab.Term Lean.Elab.Command
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__24;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__19;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__34;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__29;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__21;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__9;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__26;
lean_object* l_Lean_Expr_lit___override(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__5;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__7;
static lean_object* l_Lean_Elab_checkSimprocType___closed__8;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__18;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__25;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__14;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__11;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__8;
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__23;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__4;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__3;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__1;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__22;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__16;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__4;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__7;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__3;
static lean_object* l_Lean_Elab_checkSimprocType___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3;
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__28;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__32;
static lean_object* l_Lean_Elab_checkSimprocType___closed__9;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21;
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__13;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__22;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__7;
static lean_object* l_Lean_Elab_checkSimprocType___closed__5;
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__5;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__31;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lambda__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__15;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__27;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__20;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__33;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__23;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__1;
static lean_object* l_Lean_Elab_checkSimprocType___closed__1;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14;
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = 0;
x_16 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
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
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
x_8 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_3);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 3, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 4, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 5, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 7, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 8, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 10, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_simpGlobalConfig;
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_12);
x_15 = 0;
x_16 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_15, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
x_30 = lean_ctor_get(x_2, 5);
x_31 = lean_ctor_get(x_2, 6);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
lean_ctor_set_uint64(x_34, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 9, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 10, x_33);
x_35 = 0;
x_36 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_35, x_34, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type at '", 20, 20);
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
x_1 = lean_mk_string_unchecked("', 'Simproc' expected", 21, 21);
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
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simproc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DSimproc", 8, 8);
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
x_26 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_25, x_2, x_3, x_8);
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
x_34 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_33, x_2, x_3, x_8);
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
x_42 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_41, x_2, x_3, x_8);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Elab_checkSimprocType___closed__8;
x_44 = lean_string_dec_eq(x_15, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Elab_checkSimprocType___closed__9;
x_46 = lean_string_dec_eq(x_15, x_45);
lean_dec(x_15);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_5);
x_47 = l_Lean_MessageData_ofName(x_1);
x_48 = l_Lean_Elab_checkSimprocType___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_checkSimprocType___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_51, x_2, x_3, x_8);
return x_52;
}
else
{
uint8_t x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = 1;
x_54 = lean_box(x_53);
lean_ctor_set(x_5, 0, x_54);
return x_5;
}
}
else
{
uint8_t x_55; lean_object* x_56; 
lean_dec(x_15);
lean_dec(x_1);
x_55 = 0;
x_56 = lean_box(x_55);
lean_ctor_set(x_5, 0, x_56);
return x_5;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_57 = l_Lean_MessageData_ofName(x_1);
x_58 = l_Lean_Elab_checkSimprocType___closed__2;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Elab_checkSimprocType___closed__4;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_61, x_2, x_3, x_8);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_63 = l_Lean_MessageData_ofName(x_1);
x_64 = l_Lean_Elab_checkSimprocType___closed__2;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Elab_checkSimprocType___closed__4;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_67, x_2, x_3, x_8);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_69 = l_Lean_MessageData_ofName(x_1);
x_70 = l_Lean_Elab_checkSimprocType___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_checkSimprocType___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_73, x_2, x_3, x_8);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_75 = l_Lean_MessageData_ofName(x_1);
x_76 = l_Lean_Elab_checkSimprocType___closed__2;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Elab_checkSimprocType___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_79, x_2, x_3, x_8);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_10);
lean_free_object(x_5);
x_81 = l_Lean_MessageData_ofName(x_1);
x_82 = l_Lean_Elab_checkSimprocType___closed__2;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Elab_checkSimprocType___closed__4;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_85, x_2, x_3, x_8);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_9);
lean_free_object(x_5);
x_87 = l_Lean_MessageData_ofName(x_1);
x_88 = l_Lean_Elab_checkSimprocType___closed__2;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_Elab_checkSimprocType___closed__4;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_91, x_2, x_3, x_8);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_95 = l_Lean_ConstantInfo_type(x_93);
lean_dec(x_93);
if (lean_obj_tag(x_95) == 4)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 1)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
lean_dec(x_96);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_dec(x_97);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = l_Lean_Elab_checkSimprocType___closed__5;
x_106 = lean_string_dec_eq(x_104, x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
x_107 = l_Lean_MessageData_ofName(x_1);
x_108 = l_Lean_Elab_checkSimprocType___closed__2;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_checkSimprocType___closed__4;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_111, x_2, x_3, x_94);
return x_112;
}
else
{
lean_object* x_113; uint8_t x_114; 
x_113 = l_Lean_Elab_checkSimprocType___closed__6;
x_114 = lean_string_dec_eq(x_103, x_113);
lean_dec(x_103);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_102);
lean_dec(x_101);
x_115 = l_Lean_MessageData_ofName(x_1);
x_116 = l_Lean_Elab_checkSimprocType___closed__2;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Elab_checkSimprocType___closed__4;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_119, x_2, x_3, x_94);
return x_120;
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = l_Lean_Elab_checkSimprocType___closed__7;
x_122 = lean_string_dec_eq(x_102, x_121);
lean_dec(x_102);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_101);
x_123 = l_Lean_MessageData_ofName(x_1);
x_124 = l_Lean_Elab_checkSimprocType___closed__2;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_Elab_checkSimprocType___closed__4;
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_127, x_2, x_3, x_94);
return x_128;
}
else
{
lean_object* x_129; uint8_t x_130; 
x_129 = l_Lean_Elab_checkSimprocType___closed__8;
x_130 = lean_string_dec_eq(x_101, x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Elab_checkSimprocType___closed__9;
x_132 = lean_string_dec_eq(x_101, x_131);
lean_dec(x_101);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = l_Lean_MessageData_ofName(x_1);
x_134 = l_Lean_Elab_checkSimprocType___closed__2;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Elab_checkSimprocType___closed__4;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_137, x_2, x_3, x_94);
return x_138;
}
else
{
uint8_t x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_1);
x_139 = 1;
x_140 = lean_box(x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_94);
return x_141;
}
}
else
{
uint8_t x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_101);
lean_dec(x_1);
x_142 = 0;
x_143 = lean_box(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_94);
return x_144;
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_145 = l_Lean_MessageData_ofName(x_1);
x_146 = l_Lean_Elab_checkSimprocType___closed__2;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l_Lean_Elab_checkSimprocType___closed__4;
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_149, x_2, x_3, x_94);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_151 = l_Lean_MessageData_ofName(x_1);
x_152 = l_Lean_Elab_checkSimprocType___closed__2;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_Elab_checkSimprocType___closed__4;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_155, x_2, x_3, x_94);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_157 = l_Lean_MessageData_ofName(x_1);
x_158 = l_Lean_Elab_checkSimprocType___closed__2;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = l_Lean_Elab_checkSimprocType___closed__4;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_161, x_2, x_3, x_94);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_97);
lean_dec(x_96);
x_163 = l_Lean_MessageData_ofName(x_1);
x_164 = l_Lean_Elab_checkSimprocType___closed__2;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = l_Lean_Elab_checkSimprocType___closed__4;
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_167, x_2, x_3, x_94);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_96);
x_169 = l_Lean_MessageData_ofName(x_1);
x_170 = l_Lean_Elab_checkSimprocType___closed__2;
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Elab_checkSimprocType___closed__4;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_173, x_2, x_3, x_94);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_95);
x_175 = l_Lean_MessageData_ofName(x_1);
x_176 = l_Lean_Elab_checkSimprocType___closed__2;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Lean_Elab_checkSimprocType___closed__4;
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_179, x_2, x_3, x_94);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_5);
if (x_181 == 0)
{
return x_5;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_5, 0);
x_183 = lean_ctor_get(x_5, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_5);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_checkSimprocType___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_realizeGlobalConstNoOverload(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Elab_checkSimprocType(x_11, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_elabSimprocKeys(x_2, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Simp_registerSimproc(x_11, x_16, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
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
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocPattern", 14, 14);
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
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___lambda__1___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
x_13 = l_Lean_Elab_Command_liftTermElabM___rarg(x_12, x_2, x_3, x_4);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSimprocPattern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabSimprocPattern", 18, 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(33u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(55u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(73u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DiscrTree", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Key", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("const", 5, 5);
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
x_1 = lean_mk_string_unchecked("fvar", 4, 4);
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
x_1 = lean_mk_string_unchecked("FVarId", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
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
x_1 = lean_mk_string_unchecked("lit", 3, 3);
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
x_1 = lean_mk_string_unchecked("Literal", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natVal", 6, 6);
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
x_1 = lean_mk_string_unchecked("strVal", 6, 6);
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
x_1 = lean_mk_string_unchecked("star", 4, 4);
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
x_1 = lean_mk_string_unchecked("other", 5, 5);
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
x_1 = lean_mk_string_unchecked("arrow", 5, 5);
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
x_1 = lean_mk_string_unchecked("proj", 4, 4);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__1;
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toArray", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nil", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__9;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cons", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__3;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__13;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__14;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declare", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("registerBuiltinSimproc", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l_Lean_Elab_checkSimprocType___closed__7;
x_4 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__18;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("registerBuiltinDSimproc", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l_Lean_Elab_checkSimprocType___closed__6;
x_3 = l_Lean_Elab_checkSimprocType___closed__7;
x_4 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__21;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__22;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_realizeGlobalConstNoOverload(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Elab_checkSimprocType(x_11, x_7, x_8, x_12);
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
x_16 = l_Lean_Elab_elabSimprocKeys(x_2, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_11);
x_20 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_11);
x_21 = lean_array_to_list(x_17);
x_22 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__11;
x_23 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__15;
x_24 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Elab_Command_elabSimprocPatternBuiltin___spec__1(x_22, x_23, x_21);
x_25 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__7;
x_26 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__2;
x_27 = l_Lean_mkAppB(x_25, x_26, x_24);
lean_inc(x_11);
x_28 = l_Lean_Expr_const___override(x_11, x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
x_33 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__17;
x_34 = l_Lean_Name_append(x_11, x_33);
x_35 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_34, x_7, x_8, x_18);
x_36 = lean_unbox(x_14);
lean_dec(x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__20;
x_40 = l_Lean_mkAppN(x_39, x_32);
lean_dec(x_32);
x_41 = l_Lean_declareBuiltin(x_37, x_40, x_7, x_8, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__23;
x_45 = l_Lean_mkAppN(x_44, x_32);
lean_dec(x_32);
x_46 = l_Lean_declareBuiltin(x_42, x_45, x_7, x_8, x_43);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
return x_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_16);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocPatternBuiltin", 21, 21);
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
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
x_13 = l_Lean_Elab_Command_liftTermElabM___rarg(x_12, x_2, x_3, x_4);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSimprocPatternBuiltin(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabSimprocPatternBuiltin", 25, 25);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_checkSimprocType___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5;
x_3 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(58u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(35u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(87u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(62u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(87u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
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
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
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
l_Lean_Elab_checkSimprocType___closed__9 = _init_l_Lean_Elab_checkSimprocType___closed__9();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__9);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSimprocPattern___spec__1___rarg___closed__2);
l_Lean_Elab_Command_elabSimprocPattern___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__1);
l_Lean_Elab_Command_elabSimprocPattern___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__2);
l_Lean_Elab_Command_elabSimprocPattern___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1(lean_io_mk_world());
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
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__22 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__22);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__23 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lambda__1___closed__23);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
