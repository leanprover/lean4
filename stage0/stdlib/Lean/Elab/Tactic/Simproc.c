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
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__0;
lean_object* l_Lean_Expr_lit___override(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__1;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
static lean_object* l_Lean_Elab_checkSimprocType___closed__8;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__7;
static lean_object* l_Lean_Elab_elabSimprocPattern___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23;
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lam__1(uint8_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1;
static lean_object* l_Lean_Elab_checkSimprocType___closed__4;
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3;
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSimprocType___closed__0;
static lean_object* l_Lean_Elab_checkSimprocType___closed__5;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4;
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__0;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32;
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2;
static lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30;
static lean_object* l_Lean_Elab_checkSimprocType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_3, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 0;
x_15 = 0;
x_16 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSimprocPattern___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_elabSimprocPattern___closed__0;
x_4 = l_Lean_Elab_elabSimprocPattern___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabSimprocPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_4);
lean_ctor_set(x_6, 6, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_box(0);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lam__0___boxed), 10, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lam__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_elabSimprocPattern___closed__2;
x_17 = lean_box(1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 6, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 1, x_8);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 2, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 3, x_8);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 4, x_8);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 5, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 6, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 7, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 8, x_8);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 9, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 10, x_8);
x_20 = l_Lean_Elab_elabSimprocPattern___closed__3;
x_21 = l_Lean_Elab_Term_TermElabM_run___redArg(x_10, x_19, x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
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
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Elab_elabSimprocPattern___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Elab_elabSimprocPattern___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Elab_elabSimprocPattern(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_Meta_simpGlobalConfig;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint64_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_13);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_16);
lean_ctor_set(x_2, 0, x_10);
x_17 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_15, x_2, x_3, x_4, x_5, x_9);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
x_24 = lean_ctor_get(x_2, 5);
x_25 = lean_ctor_get(x_2, 6);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_28 = 0;
x_29 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_18);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_29);
x_30 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_23);
lean_ctor_set(x_30, 5, x_24);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*7, x_19);
lean_ctor_set_uint8(x_30, sizeof(void*)*7 + 1, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*7 + 2, x_27);
x_31 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_28, x_30, x_3, x_4, x_5, x_9);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_2, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 6);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_42 = x_2;
} else {
 lean_dec_ref(x_2);
 x_42 = lean_box(0);
}
x_43 = 0;
x_44 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_32);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_44);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 7, 3);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_36);
lean_ctor_set(x_46, 4, x_37);
lean_ctor_set(x_46, 5, x_38);
lean_ctor_set(x_46, 6, x_39);
lean_ctor_set_uint8(x_46, sizeof(void*)*7, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 1, x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 2, x_41);
x_47 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_43, x_46, x_3, x_4, x_5, x_9);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type at '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSimprocType___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', 'Simproc' expected", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSimprocType___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simproc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__8() {
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
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_18 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_19);
x_25 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_20);
x_26 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_22);
x_28 = l_Lean_Elab_checkSimprocType___closed__4;
x_29 = lean_string_dec_eq(x_27, x_28);
lean_dec_ref(x_27);
if (x_29 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Elab_checkSimprocType___closed__5;
x_31 = lean_string_dec_eq(x_26, x_30);
lean_dec_ref(x_26);
if (x_31 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Elab_checkSimprocType___closed__6;
x_33 = lean_string_dec_eq(x_25, x_32);
lean_dec_ref(x_25);
if (x_33 == 0)
{
lean_dec_ref(x_24);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Elab_checkSimprocType___closed__7;
x_35 = lean_string_dec_eq(x_24, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Elab_checkSimprocType___closed__8;
x_37 = lean_string_dec_eq(x_24, x_36);
lean_dec_ref(x_24);
if (x_37 == 0)
{
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
else
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = lean_box(x_37);
lean_ctor_set(x_5, 0, x_38);
return x_5;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec_ref(x_24);
lean_dec(x_1);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_5, 0, x_40);
return x_5;
}
}
}
}
}
else
{
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_20);
lean_dec_ref(x_19);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_19);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
}
else
{
lean_dec_ref(x_18);
lean_free_object(x_5);
x_9 = x_2;
x_10 = x_3;
goto block_17;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Elab_checkSimprocType___closed__1;
x_12 = l_Lean_MessageData_ofName(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_checkSimprocType___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_15, x_9, x_10, x_8);
return x_16;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_52; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_52 = l_Lean_ConstantInfo_type(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_52) == 4)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_58);
lean_dec_ref(x_53);
x_59 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_59);
lean_dec_ref(x_54);
x_60 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_55);
x_61 = lean_ctor_get(x_56, 1);
lean_inc_ref(x_61);
lean_dec_ref(x_56);
x_62 = l_Lean_Elab_checkSimprocType___closed__4;
x_63 = lean_string_dec_eq(x_61, x_62);
lean_dec_ref(x_61);
if (x_63 == 0)
{
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_58);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Elab_checkSimprocType___closed__5;
x_65 = lean_string_dec_eq(x_60, x_64);
lean_dec_ref(x_60);
if (x_65 == 0)
{
lean_dec_ref(x_59);
lean_dec_ref(x_58);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Elab_checkSimprocType___closed__6;
x_67 = lean_string_dec_eq(x_59, x_66);
lean_dec_ref(x_59);
if (x_67 == 0)
{
lean_dec_ref(x_58);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Elab_checkSimprocType___closed__7;
x_69 = lean_string_dec_eq(x_58, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Elab_checkSimprocType___closed__8;
x_71 = lean_string_dec_eq(x_58, x_70);
lean_dec_ref(x_58);
if (x_71 == 0)
{
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_42);
return x_73;
}
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_58);
lean_dec(x_1);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_42);
return x_76;
}
}
}
}
}
else
{
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
}
else
{
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
}
else
{
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
}
else
{
lean_dec(x_54);
lean_dec_ref(x_53);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
}
else
{
lean_dec(x_53);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
}
else
{
lean_dec_ref(x_52);
x_43 = x_2;
x_44 = x_3;
goto block_51;
}
block_51:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l_Lean_Elab_checkSimprocType___closed__1;
x_46 = l_Lean_MessageData_ofName(x_1);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_checkSimprocType___closed__3;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_49, x_43, x_44, x_42);
return x_50;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_5);
if (x_77 == 0)
{
return x_5;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_5, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
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
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
x_10 = l_Lean_realizeGlobalConstNoOverload(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = l_Lean_Elab_checkSimprocType(x_11, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
x_15 = l_Lean_Elab_elabSimprocKeys(x_2, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Simp_registerSimproc(x_11, x_16, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocPattern", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabSimprocPattern___closed__1;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___closed__0;
x_3 = l_Lean_Elab_checkSimprocType___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSimprocPattern___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
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
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
x_13 = l_Lean_Elab_Command_liftTermElabM___redArg(x_12, x_2, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSimprocPattern___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSimprocPattern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabSimprocPattern", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1;
x_4 = l_Lean_Elab_checkSimprocType___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___closed__2;
x_4 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(51u);
x_4 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(55u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(73u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(73u);
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(55u);
x_4 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DiscrTree", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Key", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("const", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fvar", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FVarId", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8;
x_3 = l_Lean_Elab_checkSimprocType___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lit", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Literal", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natVal", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15;
x_3 = l_Lean_Elab_checkSimprocType___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("strVal", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15;
x_3 = l_Lean_Elab_checkSimprocType___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("star", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("other", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arrow", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_4 = l_Lean_Elab_checkSimprocType___closed__5;
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_2);
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4;
x_13 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_10);
x_14 = l_Lean_mkNatLit(x_11);
x_15 = l_Lean_mkAppB(x_12, x_13, x_14);
x_6 = x_15;
goto block_9;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec_ref(x_4);
x_18 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7;
x_19 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11;
x_20 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_16);
x_21 = l_Lean_Expr_app___override(x_19, x_20);
x_22 = l_Lean_mkNatLit(x_17);
x_23 = l_Lean_mkAppB(x_18, x_21, x_22);
x_6 = x_23;
goto block_9;
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_4);
x_25 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14;
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18;
x_27 = l_Lean_Expr_lit___override(x_24);
x_28 = l_Lean_Expr_app___override(x_26, x_27);
x_29 = l_Lean_Expr_app___override(x_25, x_28);
x_6 = x_29;
goto block_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21;
x_31 = l_Lean_Expr_lit___override(x_24);
x_32 = l_Lean_Expr_app___override(x_30, x_31);
x_33 = l_Lean_Expr_app___override(x_25, x_32);
x_6 = x_33;
goto block_9;
}
}
case 3:
{
lean_object* x_34; 
x_34 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24;
x_6 = x_34;
goto block_9;
}
case 4:
{
lean_object* x_35; 
x_35 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27;
x_6 = x_35;
goto block_9;
}
case 5:
{
lean_object* x_36; 
x_36 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30;
x_6 = x_36;
goto block_9;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 2);
lean_inc(x_39);
lean_dec_ref(x_4);
x_40 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33;
x_41 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_37);
x_42 = l_Lean_mkNatLit(x_38);
x_43 = l_Lean_mkNatLit(x_39);
x_44 = l_Lean_mkApp3(x_40, x_41, x_42, x_43);
x_6 = x_44;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_2);
x_7 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(x_1, x_2, x_5);
x_8 = l_Lean_mkAppB(x_2, x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declare", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toArray", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5() {
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
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nil", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cons", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("registerBuiltinSimproc", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("registerBuiltinDSimproc", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_12 = l_Lean_realizeGlobalConstNoOverload(x_1, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_13);
x_15 = l_Lean_Elab_checkSimprocType(x_13, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
x_18 = l_Lean_Elab_elabSimprocKeys(x_2, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_51; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_51 = lean_unbox(x_16);
lean_dec(x_16);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Lean_Elab_checkSimprocType___closed__5;
x_53 = l_Lean_Elab_checkSimprocType___closed__6;
x_54 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13;
lean_inc_ref(x_3);
x_55 = l_Lean_Name_mkStr4(x_3, x_52, x_53, x_54);
x_21 = x_55;
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = l_Lean_Elab_checkSimprocType___closed__5;
x_57 = l_Lean_Elab_checkSimprocType___closed__6;
x_58 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14;
lean_inc_ref(x_3);
x_59 = l_Lean_Name_mkStr4(x_3, x_56, x_57, x_58);
x_21 = x_59;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_22 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1;
lean_inc(x_13);
x_23 = l_Lean_Name_append(x_13, x_22);
x_24 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_23, x_10, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_21, x_27);
lean_inc(x_13);
x_29 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_13);
x_30 = l_Lean_Elab_checkSimprocType___closed__5;
x_31 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
x_32 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
x_33 = l_Lean_Name_mkStr4(x_3, x_30, x_31, x_32);
x_34 = l_Lean_Expr_const___override(x_33, x_27);
x_35 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6;
x_36 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9;
lean_inc_ref(x_34);
x_37 = l_Lean_Expr_app___override(x_36, x_34);
x_38 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12;
lean_inc_ref(x_34);
x_39 = l_Lean_Expr_app___override(x_38, x_34);
x_40 = lean_array_to_list(x_19);
x_41 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(x_37, x_39, x_40);
lean_dec_ref(x_37);
x_42 = l_Lean_mkAppB(x_35, x_34, x_41);
x_43 = l_Lean_Expr_const___override(x_13, x_27);
x_44 = lean_mk_empty_array_with_capacity(x_4);
x_45 = lean_array_push(x_44, x_29);
x_46 = lean_array_push(x_45, x_42);
x_47 = lean_array_push(x_46, x_43);
x_48 = l_Lean_mkAppN(x_28, x_47);
lean_dec_ref(x_47);
x_49 = l_Lean_declareBuiltin(x_25, x_48, x_9, x_10, x_26);
return x_49;
}
}
else
{
uint8_t x_60; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_12);
if (x_68 == 0)
{
return x_12;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_12);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocPatternBuiltin", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___closed__0;
x_3 = l_Lean_Elab_checkSimprocType___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_checkSimprocType___closed__4;
x_6 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed), 11, 4);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_11);
x_14 = l_Lean_Elab_Command_liftTermElabM___redArg(x_13, x_2, x_3, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSimprocPatternBuiltin(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabSimprocPatternBuiltin", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0;
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2;
x_3 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1;
x_4 = l_Lean_Elab_checkSimprocType___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0;
x_3 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
x_4 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(58u);
x_4 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(62u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(87u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(87u);
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(62u);
x_4 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5;
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
x_3 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6;
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
l_Lean_Elab_elabSimprocPattern___closed__0 = _init_l_Lean_Elab_elabSimprocPattern___closed__0();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__0);
l_Lean_Elab_elabSimprocPattern___closed__1 = _init_l_Lean_Elab_elabSimprocPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__1);
l_Lean_Elab_elabSimprocPattern___closed__2 = _init_l_Lean_Elab_elabSimprocPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__2);
l_Lean_Elab_elabSimprocPattern___closed__3 = _init_l_Lean_Elab_elabSimprocPattern___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSimprocPattern___closed__3);
l_Lean_Elab_checkSimprocType___closed__0 = _init_l_Lean_Elab_checkSimprocType___closed__0();
lean_mark_persistent(l_Lean_Elab_checkSimprocType___closed__0);
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
l_Lean_Elab_Command_elabSimprocPattern___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__0);
l_Lean_Elab_Command_elabSimprocPattern___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__1);
l_Lean_Elab_Command_elabSimprocPattern___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___closed__2);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__4);
if (builtin) {res = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5);
l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6 = _init_l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1);
if (builtin) {res = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5);
l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6 = _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
