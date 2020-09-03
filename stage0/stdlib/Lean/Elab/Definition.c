// Lean compiler output
// Module: Lean.Elab.Definition
// Imports: Init Std.ShareCommon Lean.Util.CollectLevelParams Lean.Util.FoldConsts Lean.Elab.CollectFVars Lean.Elab.Command Lean.Elab.SyntheticMVars Lean.Elab.Binders Lean.Elab.DeclUtil
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
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_mkSort(lean_object*);
uint8_t l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(uint8_t);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__10;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__2;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1;
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__2;
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_Command_elabDefLike___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__1;
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen(lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__9;
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__5;
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__6;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__4;
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
lean_object* l_Lean_Elab_Command_mkDefView___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView___closed__2;
lean_object* l_Lean_Elab_Command_isDefLike___closed__4;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__3;
lean_object* l_Lean_Elab_Command_isDefLike___closed__8;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__5;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkFreshInstanceName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__11;
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__2;
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__1;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__5;
lean_object* l_Lean_Elab_Command_elabDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__6;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__9;
lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object*);
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__2;
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__9;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_Command_mkFreshInstanceName(lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__3;
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkReducibilityAttrs___closed__4;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_mkInlineAttrs___closed__4;
lean_object* l___private_Lean_Elab_Definition_1__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___boxed(lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__6;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__2;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__2;
lean_object* l___private_Lean_Elab_Definition_4__regTraceClasses(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_Command_4__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalIntro___closed__29;
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__3;
lean_object* l_Lean_Elab_Command_isDefLike___closed__5;
lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView___closed__1;
extern lean_object* l_Lean_levelOne;
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__10;
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__7;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__7;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__1;
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isTheorem(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
default: 
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 1;
return x_5;
}
}
}
}
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isExample(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkInlineAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkReducibilityAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1;
x_9 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_8);
x_10 = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2;
x_11 = l_Lean_Elab_Modifiers_addAttribute(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = 4;
x_17 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_6);
lean_ctor_set(x_17, 4, x_7);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_16);
return x_17;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_6);
lean_ctor_set(x_13, 4, x_7);
lean_ctor_set(x_13, 5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*6, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_6);
lean_ctor_set(x_14, 4, x_10);
lean_ctor_set(x_14, 5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*6, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
x_7 = lean_st_ref_take(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
lean_ctor_set(x_8, 5, x_13);
x_14 = lean_st_ref_set(x_1, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_Elab_mkFreshInstanceName(x_17, x_6);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lean_Elab_mkFreshInstanceName(x_20, x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 4);
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_29);
x_33 = lean_st_ref_set(x_1, x_32, x_9);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = l_Lean_Elab_mkFreshInstanceName(x_36, x_6);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkFreshInstanceName___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkFreshInstanceName___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_mkFreshInstanceName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arbitrary");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__29;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declValSimple");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_getMainModule___rarg(x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
x_21 = l_Lean_addMacroScope(x_19, x_20, x_15);
x_22 = l_Lean_SourceInfo_inhabited___closed__1;
x_23 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__3;
x_24 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__6;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
x_29 = lean_array_push(x_27, x_28);
x_30 = l_Lean_mkAppStx___closed__8;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__9;
x_33 = l_Lean_mkAtomFrom(x_2, x_32);
x_34 = l_Lean_mkAppStx___closed__9;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_array_push(x_35, x_31);
x_37 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__10;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_10);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_9);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_43, 5, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_42);
lean_ctor_set(x_17, 0, x_43);
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
x_47 = l_Lean_addMacroScope(x_44, x_46, x_15);
x_48 = l_Lean_SourceInfo_inhabited___closed__1;
x_49 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__3;
x_50 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__6;
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_50);
x_52 = l_Array_empty___closed__1;
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
x_55 = lean_array_push(x_53, x_54);
x_56 = l_Lean_mkAppStx___closed__8;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__9;
x_59 = l_Lean_mkAtomFrom(x_2, x_58);
x_60 = l_Lean_mkAppStx___closed__9;
x_61 = lean_array_push(x_60, x_59);
x_62 = lean_array_push(x_61, x_57);
x_63 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__10;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = l_Lean_Syntax_getArg(x_2, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_10);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_1);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_9);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_45);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_13, 0);
x_73 = lean_unsigned_to_nat(1u);
x_74 = l_Lean_Syntax_getArg(x_2, x_73);
lean_ctor_set(x_13, 0, x_10);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_1);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_9);
lean_ctor_set(x_76, 4, x_13);
lean_ctor_set(x_76, 5, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*6, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_5);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_79 = lean_unsigned_to_nat(1u);
x_80 = l_Lean_Syntax_getArg(x_2, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_10);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_83, 1, x_1);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_9);
lean_ctor_set(x_83, 4, x_81);
lean_ctor_set(x_83, 5, x_78);
lean_ctor_set_uint8(x_83, sizeof(void*)*6, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_5);
return x_84;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefViewOfConstant(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_registerInstanceAttr___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declId");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__1;
x_12 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lean_Syntax_getOptional_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Command_mkFreshInstanceName___rarg(x_4, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_mkIdentFrom(x_2, x_18);
x_20 = l_Lean_mkAppStx___closed__9;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_mkOptionalNode___closed__1;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_10);
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_2, x_27);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_9);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = l_Lean_mkIdentFrom(x_2, x_31);
x_34 = l_Lean_mkAppStx___closed__9;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_mkOptionalNode___closed__1;
x_37 = lean_array_push(x_35, x_36);
x_38 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_10);
x_41 = lean_unsigned_to_nat(3u);
x_42 = l_Lean_Syntax_getArg(x_2, x_41);
x_43 = 0;
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_12);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_9);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_32);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_10);
x_48 = lean_unsigned_to_nat(3u);
x_49 = l_Lean_Syntax_getArg(x_2, x_48);
x_50 = 0;
x_51 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_12);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_9);
lean_ctor_set(x_51, 4, x_15);
lean_ctor_set(x_51, 5, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_15, 0);
lean_inc(x_53);
lean_dec(x_15);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_10);
x_55 = lean_unsigned_to_nat(3u);
x_56 = l_Lean_Syntax_getArg(x_2, x_55);
x_57 = 0;
x_58 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_12);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_9);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*6, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
return x_59;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefViewOfInstance(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_example");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfExample___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_mkDefViewOfExample___closed__2;
x_9 = l_Lean_mkIdentFrom(x_2, x_8);
x_10 = l_Lean_mkAppStx___closed__9;
x_11 = lean_array_push(x_10, x_9);
x_12 = l_Lean_mkOptionalNode___closed__1;
x_13 = lean_array_push(x_11, x_12);
x_14 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = 2;
x_20 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_6);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_19);
return x_20;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("abbrev");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("theorem");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Meta_registerInstanceAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("example");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Command_isDefLike(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Elab_Command_isDefLike___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_isDefLike___closed__4;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Elab_Command_isDefLike___closed__6;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Command_isDefLike___closed__8;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Command_isDefLike___closed__9;
x_12 = lean_name_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_isDefLike___closed__11;
x_14 = lean_name_eq(x_2, x_13);
lean_dec(x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = 1;
return x_19;
}
}
}
lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_isDefLike(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of definition");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkDefView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkDefView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = l_Lean_Elab_Command_isDefLike___closed__2;
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Command_isDefLike___closed__4;
x_10 = lean_name_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Command_isDefLike___closed__6;
x_12 = lean_name_eq(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_isDefLike___closed__8;
x_14 = lean_name_eq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Command_isDefLike___closed__9;
x_16 = lean_name_eq(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Command_isDefLike___closed__11;
x_18 = lean_name_eq(x_6, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Command_mkDefView___closed__3;
x_20 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_19, x_3, x_4, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = l_Lean_Elab_Command_mkDefViewOfExample(x_1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_6);
x_23 = l_Lean_Elab_Command_mkDefViewOfInstance(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_6);
x_24 = l_Lean_Elab_Command_mkDefViewOfConstant(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_3);
x_25 = l_Lean_Elab_Command_mkDefViewOfTheorem(x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_3);
x_27 = l_Lean_Elab_Command_mkDefViewOfDef(x_1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_3);
x_29 = l_Lean_Elab_Command_mkDefViewOfAbbrev(x_1, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefView(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Definition_1__removeUnused___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Definition_1__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_collectUsedFVars(x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_14, x_17);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_mk_ref(x_19, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_5);
x_24 = l_Lean_Elab_Term_collectUsedFVars(x_3, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_22, x_25);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_mk_ref(x_27, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_33 = l_Array_forMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__2(x_2, x_32, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_removeUnused(x_1, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Definition_1__removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_5 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_apply_8(x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_15 = l___private_Lean_Elab_Definition_1__removeUnused(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_apply_1(x_6, x_21);
x_23 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(x_19, x_20, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelOne;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1;
x_14 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("body");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3;
x_2 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_9, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_10);
x_23 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_1, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_10);
x_26 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_9, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_30 = l_Lean_Elab_Term_levelMVarToParam(x_21, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_10);
x_35 = l_Lean_Elab_Term_levelMVarToParam(x_27, x_34, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_10);
x_39 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_33, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_10);
x_42 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = l_Std_ShareCommon_State_empty;
x_47 = lean_state_sharecommon(x_46, x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_state_sharecommon(x_49, x_43);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_120 = lean_ctor_get(x_14, 0);
lean_inc(x_120);
x_121 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__5;
x_122 = l_Lean_checkTraceOption(x_120, x_121);
lean_dec(x_120);
if (x_122 == 0)
{
x_52 = x_44;
goto block_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_inc(x_7);
x_123 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_123, 0, x_7);
x_124 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_48);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_48);
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__6;
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_MessageData_ofList___closed__3;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_51);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_51);
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_121, x_133, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_52 = x_135;
goto block_119;
}
block_119:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1;
lean_inc(x_48);
x_54 = l_Lean_CollectLevelParams_main___main(x_48, x_53);
lean_inc(x_51);
x_55 = l_Lean_CollectLevelParams_main___main(x_51, x_54);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Elab_Command_sortDeclLevelParams(x_4, x_5, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_7);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_60, x_10, x_11, x_12, x_13, x_14, x_15, x_52);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_61;
}
else
{
switch (x_6) {
case 0:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_st_ref_get(x_15, x_52);
lean_dec(x_15);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; uint32_t x_70; uint32_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_7);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_48);
lean_inc(x_51);
x_68 = l_Lean_getMaxHeight(x_66, x_51);
x_69 = lean_unbox_uint32(x_68);
lean_dec(x_68);
x_70 = 1;
x_71 = x_69 + x_70;
x_72 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_72, 0, x_71);
x_73 = lean_ctor_get(x_8, 1);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*2 + 3);
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_51);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_63, 0, x_77);
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; uint32_t x_84; uint32_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_7);
lean_ctor_set(x_81, 1, x_62);
lean_ctor_set(x_81, 2, x_48);
lean_inc(x_51);
x_82 = l_Lean_getMaxHeight(x_80, x_51);
x_83 = lean_unbox_uint32(x_82);
lean_dec(x_82);
x_84 = 1;
x_85 = x_83 + x_84;
x_86 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_86, 0, x_85);
x_87 = lean_ctor_get(x_8, 1);
x_88 = lean_ctor_get_uint8(x_87, sizeof(void*)*2 + 3);
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_51);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_79);
return x_92;
}
}
case 1:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_93 = lean_ctor_get(x_57, 0);
lean_inc(x_93);
lean_dec(x_57);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_7);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_48);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_51);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_45)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_45;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_52);
return x_98;
}
case 2:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_57);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_7);
x_99 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_100 = l_unreachable_x21___rarg(x_99);
x_101 = lean_apply_7(x_100, x_10, x_11, x_12, x_13, x_14, x_15, x_52);
return x_101;
}
case 3:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_102 = lean_ctor_get(x_57, 0);
lean_inc(x_102);
lean_dec(x_57);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_7);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_48);
x_104 = lean_ctor_get(x_8, 1);
x_105 = lean_ctor_get_uint8(x_104, sizeof(void*)*2 + 3);
x_106 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_51);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_105);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_45)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_45;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_52);
return x_109;
}
default: 
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_110 = lean_ctor_get(x_57, 0);
lean_inc(x_110);
lean_dec(x_57);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_7);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_48);
x_112 = lean_ctor_get(x_8, 1);
x_113 = lean_ctor_get_uint8(x_112, sizeof(void*)*2 + 3);
x_114 = lean_box(1);
x_115 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_51);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*3, x_113);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_45)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_45;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_52);
return x_118;
}
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_136 = !lean_is_exclusive(x_26);
if (x_136 == 0)
{
return x_26;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_26, 0);
x_138 = lean_ctor_get(x_26, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_26);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_140 = !lean_is_exclusive(x_23);
if (x_140 == 0)
{
return x_23;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_23, 0);
x_142 = lean_ctor_get(x_23, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_23);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_20);
if (x_144 == 0)
{
return x_20;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_20, 0);
x_146 = lean_ctor_get(x_20, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_20);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_17);
if (x_148 == 0)
{
return x_17;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_17, 0);
x_150 = lean_ctor_get(x_17, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_17);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 2);
x_21 = lean_ctor_get(x_13, 3);
x_22 = l_Lean_replaceRef(x_16, x_21);
lean_dec(x_16);
x_23 = l_Lean_replaceRef(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_21);
lean_dec(x_23);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_ctor_set(x_13, 3, x_24);
x_25 = 1;
x_26 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_25, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_1, 5);
lean_inc(x_29);
lean_inc(x_7);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_7);
x_31 = l_Lean_replaceRef(x_29, x_24);
lean_dec(x_29);
x_32 = l_Lean_replaceRef(x_31, x_24);
lean_dec(x_31);
x_33 = l_Lean_replaceRef(x_32, x_24);
lean_dec(x_24);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_35 = l_Lean_Elab_Term_ensureHasType(x_30, x_8, x_9, x_10, x_11, x_12, x_34, x_14, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_39 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_38, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
x_41 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
x_44 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_36, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_49 = l_Lean_Elab_DefKind_isExample(x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_44);
x_50 = l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(x_48);
x_51 = lean_box(x_48);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_6);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef_x3f___lambda__1___boxed), 16, 8);
lean_closure_set(x_52, 0, x_6);
lean_closure_set(x_52, 1, x_42);
lean_closure_set(x_52, 2, x_46);
lean_closure_set(x_52, 3, x_3);
lean_closure_set(x_52, 4, x_4);
lean_closure_set(x_52, 5, x_51);
lean_closure_set(x_52, 6, x_2);
lean_closure_set(x_52, 7, x_1);
x_53 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_46, x_42, x_50, x_52, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
lean_dec(x_6);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
lean_ctor_set(x_44, 0, x_54);
return x_44;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_44, 0);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_44);
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_58 = l_Lean_Elab_DefKind_isExample(x_57);
if (x_58 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(x_57);
x_60 = lean_box(x_57);
lean_inc(x_55);
lean_inc(x_42);
lean_inc(x_6);
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef_x3f___lambda__1___boxed), 16, 8);
lean_closure_set(x_61, 0, x_6);
lean_closure_set(x_61, 1, x_42);
lean_closure_set(x_61, 2, x_55);
lean_closure_set(x_61, 3, x_3);
lean_closure_set(x_61, 4, x_4);
lean_closure_set(x_61, 5, x_60);
lean_closure_set(x_61, 6, x_2);
lean_closure_set(x_61, 7, x_1);
x_62 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_55, x_42, x_59, x_61, x_9, x_10, x_11, x_12, x_13, x_14, x_56);
lean_dec(x_6);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_13);
lean_dec(x_14);
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
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_39);
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
lean_dec(x_13);
lean_dec(x_14);
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
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_35);
if (x_69 == 0)
{
return x_35;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_35, 0);
x_71 = lean_ctor_get(x_35, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_35);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_13);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
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
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_27);
if (x_73 == 0)
{
return x_27;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_27, 0);
x_75 = lean_ctor_get(x_27, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_27);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_13, 0);
x_78 = lean_ctor_get(x_13, 1);
x_79 = lean_ctor_get(x_13, 2);
x_80 = lean_ctor_get(x_13, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_13);
x_81 = l_Lean_replaceRef(x_16, x_80);
lean_dec(x_16);
x_82 = l_Lean_replaceRef(x_81, x_80);
lean_dec(x_81);
x_83 = l_Lean_replaceRef(x_82, x_80);
lean_dec(x_80);
lean_dec(x_82);
lean_inc(x_83);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_83);
x_85 = 1;
x_86 = lean_box(0);
lean_inc(x_14);
lean_inc(x_84);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_87 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_85, x_86, x_9, x_10, x_11, x_12, x_84, x_14, x_15);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_1, 5);
lean_inc(x_89);
lean_inc(x_7);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_7);
x_91 = l_Lean_replaceRef(x_89, x_83);
lean_dec(x_89);
x_92 = l_Lean_replaceRef(x_91, x_83);
lean_dec(x_91);
x_93 = l_Lean_replaceRef(x_92, x_83);
lean_dec(x_83);
lean_dec(x_92);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_77);
lean_ctor_set(x_94, 1, x_78);
lean_ctor_set(x_94, 2, x_79);
lean_ctor_set(x_94, 3, x_93);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_95 = l_Lean_Elab_Term_ensureHasType(x_90, x_8, x_9, x_10, x_11, x_12, x_94, x_14, x_88);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = 0;
lean_inc(x_14);
lean_inc(x_84);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_99 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_98, x_86, x_9, x_10, x_11, x_12, x_84, x_14, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_9);
x_101 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_7, x_9, x_10, x_11, x_12, x_84, x_14, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_9);
x_104 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_96, x_9, x_10, x_11, x_12, x_84, x_14, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_109 = l_Lean_Elab_DefKind_isExample(x_108);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
x_110 = l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(x_108);
x_111 = lean_box(x_108);
lean_inc(x_105);
lean_inc(x_102);
lean_inc(x_6);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef_x3f___lambda__1___boxed), 16, 8);
lean_closure_set(x_112, 0, x_6);
lean_closure_set(x_112, 1, x_102);
lean_closure_set(x_112, 2, x_105);
lean_closure_set(x_112, 3, x_3);
lean_closure_set(x_112, 4, x_4);
lean_closure_set(x_112, 5, x_111);
lean_closure_set(x_112, 6, x_2);
lean_closure_set(x_112, 7, x_1);
x_113 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_105, x_102, x_110, x_112, x_9, x_10, x_11, x_12, x_84, x_14, x_106);
lean_dec(x_6);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_84);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_107;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_96);
lean_dec(x_84);
lean_dec(x_14);
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
lean_dec(x_1);
x_116 = lean_ctor_get(x_99, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_99, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_118 = x_99;
} else {
 lean_dec_ref(x_99);
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
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_84);
lean_dec(x_14);
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
lean_dec(x_1);
x_120 = lean_ctor_get(x_95, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_95, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_122 = x_95;
} else {
 lean_dec_ref(x_95);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_14);
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
lean_dec(x_1);
x_124 = lean_ctor_get(x_87, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_87, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_126 = x_87;
} else {
 lean_dec_ref(x_87);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Elab_Command_mkDef_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
return x_18;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declValEqns");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabDefVal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equations have not been implemented yet");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDefVal___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDefVal___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_Syntax_getKind(x_1);
x_11 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__10;
x_12 = lean_name_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_13 = l_Lean_Elab_Command_elabDefVal___closed__2;
x_14 = lean_name_eq(x_10, x_13);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Elab_Command_elabDefVal___closed__5;
x_17 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = 1;
x_22 = l_Lean_Elab_Term_elabTerm(x_19, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_1, x_3, x_2, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_16 = l_Lean_Elab_Command_elabDefVal(x_15, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Command_mkDef_x3f(x_1, x_3, x_4, x_5, x_7, x_6, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_19;
}
else
{
uint8_t x_20; 
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
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_16 = lean_ctor_get(x_1, 1);
x_51 = 2;
x_52 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_53 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_2, x_51, x_16, x_52, x_13, x_14, x_15);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_3, 4);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 3);
lean_inc(x_59);
x_60 = l_Lean_replaceRef(x_4, x_59);
x_61 = l_Lean_replaceRef(x_60, x_59);
lean_dec(x_60);
x_62 = l_Lean_replaceRef(x_61, x_59);
lean_dec(x_59);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_62);
x_64 = 0;
x_65 = lean_box(0);
lean_inc(x_11);
lean_inc(x_9);
x_66 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(x_64, x_65, x_9, x_10, x_11, x_12, x_63, x_14, x_55);
lean_dec(x_63);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_3, 5);
lean_inc(x_69);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_67);
x_70 = l_Lean_Elab_Command_elabDefVal(x_69, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_73 = l_Lean_Elab_Command_mkDef_x3f(x_3, x_2, x_5, x_6, x_7, x_8, x_67, x_71, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_17 = x_74;
x_18 = x_75;
goto block_50;
}
else
{
uint8_t x_76; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
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
lean_dec(x_67);
lean_dec(x_14);
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
x_80 = !lean_is_exclusive(x_70);
if (x_80 == 0)
{
return x_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_70, 0);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_70);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
lean_dec(x_53);
x_85 = lean_ctor_get(x_54, 0);
lean_inc(x_85);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_86 = l_Lean_Elab_Term_elabType(x_85, x_9, x_10, x_11, x_12, x_13, x_14, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = 0;
x_90 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_91 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_89, x_90, x_9, x_10, x_11, x_12, x_13, x_14, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_9);
x_93 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_87, x_9, x_10, x_11, x_12, x_13, x_14, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_97 = l_Lean_Elab_DefKind_isTheorem(x_96);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_94);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__1), 14, 6);
lean_closure_set(x_98, 0, x_3);
lean_closure_set(x_98, 1, x_94);
lean_closure_set(x_98, 2, x_2);
lean_closure_set(x_98, 3, x_5);
lean_closure_set(x_98, 4, x_6);
lean_closure_set(x_98, 5, x_8);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_99 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(x_7, x_8, x_94, x_97, x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_95);
lean_dec(x_8);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_17 = x_100;
x_18 = x_101;
goto block_50;
}
else
{
uint8_t x_102; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_87);
lean_dec(x_14);
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
x_106 = !lean_is_exclusive(x_91);
if (x_106 == 0)
{
return x_91;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_91, 0);
x_108 = lean_ctor_get(x_91, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_91);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_14);
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
x_110 = !lean_is_exclusive(x_86);
if (x_110 == 0)
{
return x_86;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_86, 0);
x_112 = lean_ctor_get(x_86, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_86);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_14);
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
x_114 = !lean_is_exclusive(x_53);
if (x_114 == 0)
{
return x_53;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_53, 0);
x_116 = lean_ctor_get(x_53, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_53);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
block_50:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_21);
x_22 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_13);
lean_inc(x_9);
x_24 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 0;
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_28 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_2, x_26, x_16, x_27, x_13, x_14, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_13);
x_30 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_2, x_32, x_16, x_27, x_13, x_14, x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
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
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
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
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_inc(x_5);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__2___boxed), 15, 7);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Term_withLevelNames___rarg(x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 6);
lean_dec(x_11);
lean_ctor_set(x_2, 6, x_9);
x_12 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Elab_Command_expandDeclId(x_15, x_16, x_2, x_3, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 13, 5);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_13);
lean_closure_set(x_23, 4, x_21);
x_24 = lean_st_ref_get(x_3, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Command_4__getVarDecls(x_25);
lean_dec(x_25);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_23);
x_29 = l_Lean_Elab_Command_liftTermElabM___rarg(x_22, x_28, x_2, x_3, x_26);
lean_dec(x_2);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_ctor_get(x_2, 4);
x_39 = lean_ctor_get(x_2, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_38);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_9);
x_41 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_inc(x_40);
x_46 = l_Lean_Elab_Command_expandDeclId(x_44, x_45, x_40, x_3, x_43);
lean_dec(x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 2);
lean_inc(x_50);
lean_dec(x_47);
lean_inc(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 13, 5);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_45);
lean_closure_set(x_52, 2, x_49);
lean_closure_set(x_52, 3, x_42);
lean_closure_set(x_52, 4, x_50);
x_53 = lean_st_ref_get(x_3, x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l___private_Lean_Elab_Command_4__getVarDecls(x_54);
lean_dec(x_54);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_57, 0, x_56);
lean_closure_set(x_57, 1, x_52);
x_58 = l_Lean_Elab_Command_liftTermElabM___rarg(x_51, x_57, x_40, x_3, x_55);
lean_dec(x_40);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_1);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_61 = x_46;
} else {
 lean_dec_ref(x_46);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_Command_elabDefLike___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_applyAttributes___at_Lean_Elab_Command_elabDefLike___spec__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabDefLike___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabDefLike(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Definition_4__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_ShareCommon(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
lean_object* initialize_Lean_Elab_CollectFVars(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Definition(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_ShareCommon(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1);
l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__1);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__2);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__3 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__3);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__4 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__4);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__5 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__5);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__6 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__6);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__7 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__7);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__8 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__8);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__9 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__9);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__10 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__10);
l_Lean_Elab_Command_mkDefViewOfInstance___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1);
l_Lean_Elab_Command_mkDefViewOfInstance___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2);
l_Lean_Elab_Command_mkDefViewOfInstance___closed__3 = _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfInstance___closed__3);
l_Lean_Elab_Command_mkDefViewOfExample___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfExample___closed__1);
l_Lean_Elab_Command_mkDefViewOfExample___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfExample___closed__2);
l_Lean_Elab_Command_isDefLike___closed__1 = _init_l_Lean_Elab_Command_isDefLike___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__1);
l_Lean_Elab_Command_isDefLike___closed__2 = _init_l_Lean_Elab_Command_isDefLike___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__2);
l_Lean_Elab_Command_isDefLike___closed__3 = _init_l_Lean_Elab_Command_isDefLike___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__3);
l_Lean_Elab_Command_isDefLike___closed__4 = _init_l_Lean_Elab_Command_isDefLike___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__4);
l_Lean_Elab_Command_isDefLike___closed__5 = _init_l_Lean_Elab_Command_isDefLike___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__5);
l_Lean_Elab_Command_isDefLike___closed__6 = _init_l_Lean_Elab_Command_isDefLike___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__6);
l_Lean_Elab_Command_isDefLike___closed__7 = _init_l_Lean_Elab_Command_isDefLike___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__7);
l_Lean_Elab_Command_isDefLike___closed__8 = _init_l_Lean_Elab_Command_isDefLike___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__8);
l_Lean_Elab_Command_isDefLike___closed__9 = _init_l_Lean_Elab_Command_isDefLike___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__9);
l_Lean_Elab_Command_isDefLike___closed__10 = _init_l_Lean_Elab_Command_isDefLike___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__10);
l_Lean_Elab_Command_isDefLike___closed__11 = _init_l_Lean_Elab_Command_isDefLike___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__11);
l_Lean_Elab_Command_mkDefView___closed__1 = _init_l_Lean_Elab_Command_mkDefView___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefView___closed__1);
l_Lean_Elab_Command_mkDefView___closed__2 = _init_l_Lean_Elab_Command_mkDefView___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefView___closed__2);
l_Lean_Elab_Command_mkDefView___closed__3 = _init_l_Lean_Elab_Command_mkDefView___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDefView___closed__3);
l___private_Lean_Elab_Definition_1__removeUnused___closed__1 = _init_l___private_Lean_Elab_Definition_1__removeUnused___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Definition_1__removeUnused___closed__1);
l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1 = _init_l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1);
l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1 = _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1);
l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__2 = _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__2);
l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3 = _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__3);
l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__4 = _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__4);
l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__5 = _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__5);
l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__6 = _init_l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__6);
l_Lean_Elab_Command_elabDefVal___closed__1 = _init_l_Lean_Elab_Command_elabDefVal___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__1);
l_Lean_Elab_Command_elabDefVal___closed__2 = _init_l_Lean_Elab_Command_elabDefVal___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__2);
l_Lean_Elab_Command_elabDefVal___closed__3 = _init_l_Lean_Elab_Command_elabDefVal___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__3);
l_Lean_Elab_Command_elabDefVal___closed__4 = _init_l_Lean_Elab_Command_elabDefVal___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__4);
l_Lean_Elab_Command_elabDefVal___closed__5 = _init_l_Lean_Elab_Command_elabDefVal___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__5);
res = l___private_Lean_Elab_Definition_4__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
