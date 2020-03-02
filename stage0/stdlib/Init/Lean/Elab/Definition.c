// Lean compiler output
// Module: Init.Lean.Elab.Definition
// Imports: Init.Lean.Util.CollectLevelParams Init.Lean.Util.CollectFVars Init.Lean.Elab.DeclModifiers Init.Lean.Elab.Binders
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__2;
lean_object* l_Lean_Elab_Command_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_9__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_collectUsedFVarsAtFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isExample(uint8_t);
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_collectUsedFVarsAtFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isTheorem___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen(lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
lean_object* l_Lean_Elab_Command_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Definition_1__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen_x27(lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isDefOrOpaque___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
extern lean_object* l_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__6;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_collectUsedFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_removeUnused___closed__1;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isDefOrOpaque(uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Command_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isTheorem(uint8_t x_1) {
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
lean_object* l_Lean_Elab_Command_DefKind_isTheorem___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Command_DefKind_isTheorem(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Elab_Command_DefKind_isDefOrOpaque(uint8_t x_1) {
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
lean_object* l_Lean_Elab_Command_DefKind_isDefOrOpaque___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Command_DefKind_isDefOrOpaque(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Elab_Command_DefKind_isExample(uint8_t x_1) {
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
lean_object* l_Lean_Elab_Command_DefKind_isExample___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Command_DefKind_isExample(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_collectUsedFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Term_instantiateMVars(x_1, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_CollectFVars_main___main(x_8, x_2);
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
x_12 = l_Lean_CollectFVars_main___main(x_10, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Command_collectUsedFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_inferType(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
x_17 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_5, x_15, x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_13;
x_5 = x_18;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_collectUsedFVarsAtFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1(x_1, x_3, x_3, x_6, x_2, x_4, x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_collectUsedFVarsAtFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_collectUsedFVarsAtFVars(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_array_fget(x_3, x_12);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_fvarId_x21(x_13);
x_26 = l_Lean_NameSet_contains(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_inc(x_25);
x_27 = lean_local_ctx_erase(x_17, x_25);
x_28 = l_Lean_LocalInstances_erase(x_20, x_25);
lean_dec(x_25);
lean_ctor_set(x_14, 0, x_28);
lean_ctor_set(x_6, 0, x_27);
x_4 = x_12;
x_5 = lean_box(0);
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_15, 0);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_13);
x_33 = l_Lean_Elab_Term_inferType(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_7);
x_36 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_23, x_34, x_7, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_push(x_22, x_13);
lean_ctor_set(x_15, 1, x_37);
lean_ctor_set(x_15, 0, x_39);
x_4 = x_12;
x_5 = lean_box(0);
x_8 = x_38;
goto _start;
}
else
{
uint8_t x_41; 
lean_free_object(x_15);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_14);
lean_dec(x_20);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_13);
x_45 = l_Lean_Elab_Term_inferType(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_7);
x_48 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_23, x_46, x_7, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_array_push(x_22, x_13);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_14, 1, x_52);
x_4 = x_12;
x_5 = lean_box(0);
x_8 = x_50;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_14);
lean_dec(x_20);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
lean_dec(x_14);
x_59 = lean_ctor_get(x_15, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = l_Lean_Expr_fvarId_x21(x_13);
x_63 = l_Lean_NameSet_contains(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_13);
lean_inc(x_62);
x_64 = lean_local_ctx_erase(x_17, x_62);
x_65 = l_Lean_LocalInstances_erase(x_58, x_62);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_15);
lean_ctor_set(x_6, 1, x_66);
lean_ctor_set(x_6, 0, x_64);
x_4 = x_12;
x_5 = lean_box(0);
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_62);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_68 = x_15;
} else {
 lean_dec_ref(x_15);
 x_68 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_13);
x_69 = l_Lean_Elab_Term_inferType(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_7);
x_72 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_60, x_70, x_7, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_push(x_59, x_13);
if (lean_is_scalar(x_68)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_68;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_58);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_6, 1, x_77);
x_4 = x_12;
x_5 = lean_box(0);
x_8 = x_74;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_69, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_81 = x_69;
} else {
 lean_dec_ref(x_69);
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
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_6, 0);
lean_inc(x_83);
lean_dec(x_6);
x_84 = lean_ctor_get(x_14, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_85 = x_14;
} else {
 lean_dec_ref(x_14);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_15, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = l_Lean_Expr_fvarId_x21(x_13);
x_90 = l_Lean_NameSet_contains(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_13);
lean_inc(x_89);
x_91 = lean_local_ctx_erase(x_83, x_89);
x_92 = l_Lean_LocalInstances_erase(x_84, x_89);
lean_dec(x_89);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_15);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_96 = x_15;
} else {
 lean_dec_ref(x_15);
 x_96 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_13);
x_97 = l_Lean_Elab_Term_inferType(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_7);
x_100 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_87, x_98, x_7, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_array_push(x_86, x_13);
if (lean_is_scalar(x_96)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_96;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
if (lean_is_scalar(x_85)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_85;
}
lean_ctor_set(x_105, 0, x_84);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_83);
lean_ctor_set(x_106, 1, x_105);
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_106;
x_8 = x_102;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_96);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_108 = lean_ctor_get(x_97, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_110 = x_97;
} else {
 lean_dec_ref(x_97);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_7);
lean_dec(x_4);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_6);
lean_ctor_set(x_112, 1, x_8);
return x_112;
}
}
}
lean_object* _init_l_Lean_Elab_Command_removeUnused___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_HashSet_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_Elab_Command_removeUnused___closed__1;
lean_inc(x_6);
x_9 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_8, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
x_12 = l_Lean_Elab_Command_collectUsedFVars(x_1, x_10, x_4, x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_16 = l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1(x_1, x_3, x_3, x_15, x_13, x_6, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getLocalInsts(x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getLCtx(x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_empty___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_get_size(x_2);
x_30 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1(x_1, x_2, x_2, x_29, lean_box(0), x_28, x_6, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_dec(x_42);
x_43 = l_Array_reverseAux___main___rarg(x_41, x_15);
lean_ctor_set(x_33, 1, x_43);
lean_ctor_set(x_33, 0, x_38);
lean_ctor_set(x_32, 0, x_36);
lean_ctor_set(x_30, 0, x_32);
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = l_Array_reverseAux___main___rarg(x_44, x_15);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_32, 1, x_46);
lean_ctor_set(x_32, 0, x_36);
lean_ctor_set(x_30, 0, x_32);
return x_30;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
x_50 = l_Array_reverseAux___main___rarg(x_48, x_15);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_30, 0, x_52);
return x_30;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_dec(x_30);
x_54 = lean_ctor_get(x_31, 0);
lean_inc(x_54);
lean_dec(x_31);
x_55 = lean_ctor_get(x_32, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_56 = x_32;
} else {
 lean_dec_ref(x_32);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_33, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_58 = x_33;
} else {
 lean_dec_ref(x_33);
 x_58 = lean_box(0);
}
x_59 = l_Array_reverseAux___main___rarg(x_57, x_15);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_30);
if (x_63 == 0)
{
return x_30;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_30, 0);
x_65 = lean_ctor_get(x_30, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_30);
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
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_withUsedWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_6 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_apply_3(x_7, x_2, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_inc(x_8);
x_11 = l_Lean_Elab_Command_removeUnused(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_dec(x_23);
lean_ctor_set(x_14, 2, x_17);
lean_ctor_set(x_14, 1, x_16);
x_24 = lean_apply_3(x_7, x_18, x_8, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 3);
x_27 = lean_ctor_get(x_14, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_28, 2, x_17);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_8, 0, x_28);
x_29 = lean_apply_3(x_7, x_18, x_8, x_15);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_8, 1);
x_31 = lean_ctor_get(x_8, 2);
x_32 = lean_ctor_get(x_8, 3);
x_33 = lean_ctor_get(x_8, 4);
x_34 = lean_ctor_get(x_8, 5);
x_35 = lean_ctor_get(x_8, 6);
x_36 = lean_ctor_get(x_8, 7);
x_37 = lean_ctor_get(x_8, 8);
x_38 = lean_ctor_get(x_8, 9);
x_39 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_40 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_41 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 4);
lean_inc(x_44);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_45 = x_14;
} else {
 lean_dec_ref(x_14);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 5, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_16);
lean_ctor_set(x_46, 2, x_17);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_44);
x_47 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_30);
lean_ctor_set(x_47, 2, x_31);
lean_ctor_set(x_47, 3, x_32);
lean_ctor_set(x_47, 4, x_33);
lean_ctor_set(x_47, 5, x_34);
lean_ctor_set(x_47, 6, x_35);
lean_ctor_set(x_47, 7, x_36);
lean_ctor_set(x_47, 8, x_37);
lean_ctor_set(x_47, 9, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*10, x_39);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 1, x_40);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 2, x_41);
x_48 = lean_apply_3(x_7, x_18, x_47, x_15);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_withUsedWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withUsedWhen___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withUsedWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Elab_Command_withUsedWhen___rarg(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_withUsedWhen_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
x_10 = l_Lean_Elab_Command_withUsedWhen___rarg(x_1, x_2, x_3, x_4, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_withUsedWhen_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withUsedWhen_x27___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withUsedWhen_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Elab_Command_withUsedWhen_x27___rarg(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HashSet_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("body");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_3, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l_Lean_Elab_Term_mkForall(x_1, x_10, x_14, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
x_19 = l_Lean_Elab_Term_mkLambda(x_1, x_2, x_4, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_11);
x_22 = l_Lean_Elab_Term_mkLambda(x_1, x_10, x_20, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
x_25 = l_Lean_Elab_Term_levelMVarToParam(x_17, x_11, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
x_28 = l_Lean_Elab_Term_levelMVarToParam(x_23, x_11, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_11);
x_31 = l_Lean_Elab_Term_instantiateMVars(x_1, x_26, x_11, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_11);
x_34 = l_Lean_Elab_Term_instantiateMVars(x_5, x_29, x_11, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_69 = l_Lean_Elab_Term_getOptions(x_11, x_36);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Command_mkDef___lambda__1___closed__6;
x_73 = l_Lean_checkTraceOption(x_70, x_72);
lean_dec(x_70);
if (x_73 == 0)
{
x_38 = x_71;
goto block_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_35);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_35);
x_75 = l_Lean_Elab_Term_logTrace(x_72, x_1, x_74, x_11, x_71);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_38 = x_76;
goto block_68;
}
block_68:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_32);
x_40 = l_Lean_CollectLevelParams_main___main(x_32, x_39);
lean_inc(x_35);
x_41 = l_Lean_CollectLevelParams_main___main(x_35, x_40);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_Command_sortDeclLevelParams(x_6, x_42);
switch (x_7) {
case 0:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_11);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_32);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*2 + 3);
x_47 = l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_37)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_37;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_8);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_32);
x_53 = lean_task_pure(x_35);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_37)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_37;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
return x_57;
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_43);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_8);
x_58 = l___private_Init_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___closed__1;
x_59 = l_unreachable_x21___rarg(x_58);
x_60 = lean_apply_2(x_59, x_11, x_38);
return x_60;
}
default: 
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_43);
lean_ctor_set(x_61, 2, x_32);
x_62 = lean_ctor_get(x_9, 1);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*2 + 3);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_35);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_63);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_37)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_37;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_38);
return x_67;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_22);
if (x_77 == 0)
{
return x_22;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_22, 0);
x_79 = lean_ctor_get(x_22, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_22);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_81 = !lean_is_exclusive(x_19);
if (x_81 == 0)
{
return x_19;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_19, 0);
x_83 = lean_ctor_get(x_19, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_19);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_16);
if (x_85 == 0)
{
return x_16;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_16, 0);
x_87 = lean_ctor_get(x_16, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_16);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_13);
if (x_89 == 0)
{
return x_13;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_13, 0);
x_91 = lean_ctor_get(x_13, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_13);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = 1;
x_12 = lean_box(0);
lean_inc(x_8);
x_13 = l___private_Init_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
lean_inc(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_6);
lean_inc(x_8);
lean_inc(x_15);
x_17 = l_Lean_Elab_Term_ensureHasType(x_15, x_16, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
lean_inc(x_8);
x_21 = l___private_Init_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_20, x_12, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_8);
x_23 = l_Lean_Elab_Term_instantiateMVars(x_10, x_6, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
x_26 = l_Lean_Elab_Term_instantiateMVars(x_15, x_18, x_8, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_31 = l_Lean_Elab_Command_DefKind_isExample(x_30);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_26);
x_32 = l_Lean_Elab_Command_DefKind_isDefOrOpaque(x_30);
x_33 = lean_box(x_30);
lean_inc(x_28);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_10);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 12, 9);
lean_closure_set(x_34, 0, x_10);
lean_closure_set(x_34, 1, x_5);
lean_closure_set(x_34, 2, x_24);
lean_closure_set(x_34, 3, x_28);
lean_closure_set(x_34, 4, x_15);
lean_closure_set(x_34, 5, x_3);
lean_closure_set(x_34, 6, x_33);
lean_closure_set(x_34, 7, x_2);
lean_closure_set(x_34, 8, x_1);
x_35 = l_Lean_Elab_Command_withUsedWhen___rarg(x_10, x_4, x_5, x_28, x_24, x_32, x_34, x_8, x_29);
lean_dec(x_5);
lean_dec(x_10);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_40 = l_Lean_Elab_Command_DefKind_isExample(x_39);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lean_Elab_Command_DefKind_isDefOrOpaque(x_39);
x_42 = lean_box(x_39);
lean_inc(x_37);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_10);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 12, 9);
lean_closure_set(x_43, 0, x_10);
lean_closure_set(x_43, 1, x_5);
lean_closure_set(x_43, 2, x_24);
lean_closure_set(x_43, 3, x_37);
lean_closure_set(x_43, 4, x_15);
lean_closure_set(x_43, 5, x_3);
lean_closure_set(x_43, 6, x_42);
lean_closure_set(x_43, 7, x_2);
lean_closure_set(x_43, 8, x_1);
x_44 = l_Lean_Elab_Command_withUsedWhen___rarg(x_10, x_4, x_5, x_37, x_24, x_41, x_43, x_8, x_38);
lean_dec(x_5);
lean_dec(x_10);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
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
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Elab_Command_mkDef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equations have not been implemented yet");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDefVal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDefVal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDefVal___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
x_7 = lean_name_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_8 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_9 = lean_name_eq(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Command_elabDefVal___closed__3;
x_12 = l_Lean_Elab_Term_throwError___rarg(x_1, x_11, x_3, x_4);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = 1;
x_17 = l_Lean_Elab_Term_elabTerm(x_14, x_15, x_16, x_3, x_4);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Syntax_getId(x_10);
x_14 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(x_13, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_3 = x_12;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_17 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_10, x_13, x_5, x_6);
lean_dec(x_10);
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
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_elabDefVal(x_9, x_2, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_mkDef(x_1, x_3, x_4, x_6, x_5, x_2, x_11, x_7, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_8);
x_13 = l_Lean_Elab_Term_mkFreshTypeMVar(x_2, x_11, x_12, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_inc(x_8);
lean_inc(x_14);
x_17 = l_Lean_Elab_Command_elabDefVal(x_16, x_14, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_mkDef(x_1, x_3, x_4, x_5, x_7, x_14, x_18, x_8, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_25);
x_26 = l_Lean_Elab_Term_elabType(x_25, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 0;
x_30 = lean_box(0);
lean_inc(x_8);
x_31 = l___private_Init_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_29, x_30, x_8, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_8);
x_33 = l_Lean_Elab_Term_instantiateMVars(x_25, x_27, x_8, x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_37 = l_Lean_Elab_Command_DefKind_isTheorem(x_36);
lean_inc(x_7);
lean_inc(x_34);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__1), 8, 5);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_34);
lean_closure_set(x_38, 2, x_3);
lean_closure_set(x_38, 3, x_4);
lean_closure_set(x_38, 4, x_7);
x_39 = l_Lean_Elab_Command_withUsedWhen_x27___rarg(x_6, x_5, x_7, x_34, x_37, x_38, x_8, x_35);
lean_dec(x_7);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_44; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
return x_26;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_26);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = l_Lean_Syntax_getArgs(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__2___boxed), 9, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_4);
x_11 = l_Lean_Elab_Term_elabBinders___rarg(x_9, x_10, x_6, x_7);
lean_dec(x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = l_Lean_Elab_Command_expandDeclId(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_getLevelNames(x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_399; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_399 = l_Lean_Syntax_isNone(x_8);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_400 = lean_unsigned_to_nat(1u);
x_401 = l_Lean_Syntax_getArg(x_8, x_400);
x_402 = l_Lean_Syntax_getArgs(x_401);
lean_dec(x_401);
x_403 = lean_unsigned_to_nat(2u);
x_404 = lean_unsigned_to_nat(0u);
x_405 = l_Array_empty___closed__1;
x_406 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_403, x_402, x_404, x_405);
lean_dec(x_402);
lean_inc(x_2);
lean_inc(x_10);
x_407 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5(x_8, x_406, x_404, x_10, x_2, x_11);
lean_dec(x_406);
lean_dec(x_8);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_12 = x_408;
x_13 = x_409;
goto block_398;
}
else
{
uint8_t x_410; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_410 = !lean_is_exclusive(x_407);
if (x_410 == 0)
{
return x_407;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_407, 0);
x_412 = lean_ctor_get(x_407, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_407);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
else
{
lean_dec(x_8);
lean_inc(x_10);
x_12 = x_10;
x_13 = x_11;
goto block_398;
}
block_398:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_extractMacroScopes(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_name_mk_string(x_20, x_19);
lean_ctor_set(x_14, 0, x_21);
x_22 = l_Lean_MacroScopesView_review(x_14);
x_23 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_24 = 1;
lean_inc(x_2);
lean_inc(x_18);
x_25 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_5, x_23, x_24, x_18, x_2, x_13);
lean_dec(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_2);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__1(x_12, x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_81; lean_object* x_82; lean_object* x_93; lean_object* x_94; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_93 = lean_ctor_get(x_1, 1);
lean_inc(x_93);
lean_inc(x_2);
x_94 = l_Lean_Elab_Command_mkDeclName(x_93, x_22, x_2, x_28);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_123 = 2;
x_124 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_95);
x_125 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_95, x_123, x_97, x_124, x_2, x_96);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_2);
x_127 = l_Lean_Elab_Command_getLevelNames(x_2, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_95);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_95);
lean_inc(x_4);
lean_inc(x_95);
x_131 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 7, 4);
lean_closure_set(x_131, 0, x_1);
lean_closure_set(x_131, 1, x_95);
lean_closure_set(x_131, 2, x_128);
lean_closure_set(x_131, 3, x_4);
lean_inc(x_2);
x_132 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_133);
lean_dec(x_133);
lean_inc(x_2);
x_136 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_2, x_137, x_130);
x_140 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_137);
lean_dec(x_137);
x_141 = l_Lean_Elab_Term_elabBinders___rarg(x_135, x_131, x_139, x_140);
lean_dec(x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_2);
x_144 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get(x_143, 2);
lean_inc(x_149);
lean_dec(x_143);
x_150 = !lean_is_exclusive(x_146);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_146, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_146, 0);
lean_dec(x_152);
lean_ctor_set(x_146, 1, x_149);
lean_ctor_set(x_146, 0, x_148);
lean_inc(x_2);
x_153 = l___private_Init_Lean_Elab_Command_3__setState(x_146, x_2, x_147);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_98 = x_142;
x_99 = x_154;
goto block_122;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_142);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_81 = x_155;
x_82 = x_156;
goto block_92;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_146, 2);
x_158 = lean_ctor_get(x_146, 3);
x_159 = lean_ctor_get(x_146, 4);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_146);
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_149);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_158);
lean_ctor_set(x_160, 4, x_159);
lean_inc(x_2);
x_161 = l___private_Init_Lean_Elab_Command_3__setState(x_160, x_2, x_147);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_98 = x_142;
x_99 = x_162;
goto block_122;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_142);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_81 = x_163;
x_82 = x_164;
goto block_92;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_165 = lean_ctor_get(x_144, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_144, 1);
lean_inc(x_166);
lean_dec(x_144);
x_81 = x_165;
x_82 = x_166;
goto block_92;
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_141, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_168 = lean_ctor_get(x_141, 1);
lean_inc(x_168);
lean_dec(x_141);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_2);
x_170 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_138);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_168, 2);
lean_inc(x_175);
lean_dec(x_168);
x_176 = !lean_is_exclusive(x_172);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_172, 1);
lean_dec(x_177);
x_178 = lean_ctor_get(x_172, 0);
lean_dec(x_178);
lean_ctor_set(x_172, 1, x_175);
lean_ctor_set(x_172, 0, x_174);
lean_inc(x_2);
x_179 = l___private_Init_Lean_Elab_Command_3__setState(x_172, x_2, x_173);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_81 = x_169;
x_82 = x_180;
goto block_92;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_169);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_81 = x_181;
x_82 = x_182;
goto block_92;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_172, 2);
x_184 = lean_ctor_get(x_172, 3);
x_185 = lean_ctor_get(x_172, 4);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_172);
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_174);
lean_ctor_set(x_186, 1, x_175);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set(x_186, 4, x_185);
lean_inc(x_2);
x_187 = l___private_Init_Lean_Elab_Command_3__setState(x_186, x_2, x_173);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_81 = x_169;
x_82 = x_188;
goto block_92;
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_169);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_81 = x_189;
x_82 = x_190;
goto block_92;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_169);
lean_dec(x_168);
x_191 = lean_ctor_get(x_170, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_170, 1);
lean_inc(x_192);
lean_dec(x_170);
x_81 = x_191;
x_82 = x_192;
goto block_92;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_141);
x_193 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_194 = l_unreachable_x21___rarg(x_193);
lean_inc(x_2);
x_195 = lean_apply_2(x_194, x_2, x_138);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_98 = x_196;
x_99 = x_197;
goto block_122;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
lean_dec(x_195);
x_81 = x_198;
x_82 = x_199;
goto block_92;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_135);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_200 = lean_ctor_get(x_136, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_136, 1);
lean_inc(x_201);
lean_dec(x_136);
x_81 = x_200;
x_82 = x_201;
goto block_92;
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_202 = lean_ctor_get(x_132, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_132, 1);
lean_inc(x_203);
lean_dec(x_132);
x_81 = x_202;
x_82 = x_203;
goto block_92;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_204 = lean_ctor_get(x_127, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_127, 1);
lean_inc(x_205);
lean_dec(x_127);
x_81 = x_204;
x_82 = x_205;
goto block_92;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_206 = lean_ctor_get(x_125, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_125, 1);
lean_inc(x_207);
lean_dec(x_125);
x_81 = x_206;
x_82 = x_207;
goto block_92;
}
block_122:
{
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_4);
x_100 = lean_box(0);
x_29 = x_100;
x_30 = x_99;
goto block_80;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_2);
x_102 = l_Lean_Elab_Command_addDecl(x_4, x_101, x_2, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = 0;
x_105 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_95);
x_106 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_95, x_104, x_97, x_105, x_2, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
lean_inc(x_2);
x_108 = l_Lean_Elab_Command_compileDecl(x_4, x_101, x_2, x_107);
lean_dec(x_101);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = 1;
lean_inc(x_2);
x_111 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_95, x_110, x_97, x_105, x_2, x_109);
lean_dec(x_97);
lean_dec(x_4);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_29 = x_112;
x_30 = x_113;
goto block_80;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_18);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_81 = x_114;
x_82 = x_115;
goto block_92;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_dec(x_108);
x_81 = x_116;
x_82 = x_117;
goto block_92;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_101);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_118 = lean_ctor_get(x_106, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
x_81 = x_118;
x_82 = x_119;
goto block_92;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_101);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_4);
x_120 = lean_ctor_get(x_102, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_102, 1);
lean_inc(x_121);
lean_dec(x_102);
x_81 = x_120;
x_82 = x_121;
goto block_92;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_93);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_208 = lean_ctor_get(x_94, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_94, 1);
lean_inc(x_209);
lean_dec(x_94);
x_81 = x_208;
x_82 = x_209;
goto block_92;
}
block_80:
{
lean_object* x_31; 
lean_inc(x_2);
lean_inc(x_10);
x_31 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__2(x_10, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_2);
x_33 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 2);
x_38 = l_Lean_Name_getNumParts___main(x_18);
lean_dec(x_18);
x_39 = l_List_drop___main___rarg(x_38, x_37);
lean_dec(x_37);
lean_ctor_set(x_34, 2, x_39);
x_40 = l___private_Init_Lean_Elab_Command_3__setState(x_34, x_2, x_35);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_29);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
x_51 = lean_ctor_get(x_34, 2);
x_52 = lean_ctor_get(x_34, 3);
x_53 = lean_ctor_get(x_34, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_54 = l_Lean_Name_getNumParts___main(x_18);
lean_dec(x_18);
x_55 = l_List_drop___main___rarg(x_54, x_51);
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_53);
x_57 = l___private_Init_Lean_Elab_Command_3__setState(x_56, x_2, x_35);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_29);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_29);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_29);
lean_dec(x_18);
x_69 = lean_ctor_get(x_31, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_31, 1);
lean_inc(x_70);
lean_dec(x_31);
x_71 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__3(x_10, x_2, x_70);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_69);
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
block_92:
{
lean_object* x_83; 
x_83 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__4(x_10, x_2, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_81);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_27);
if (x_210 == 0)
{
return x_27;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_27, 0);
x_212 = lean_ctor_get(x_27, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_27);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_25);
if (x_214 == 0)
{
return x_25;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_25, 0);
x_216 = lean_ctor_get(x_25, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_25);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; 
x_218 = lean_ctor_get(x_14, 1);
x_219 = lean_ctor_get(x_14, 2);
x_220 = lean_ctor_get(x_14, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_14);
x_221 = lean_ctor_get(x_15, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_15, 1);
lean_inc(x_222);
lean_dec(x_15);
x_223 = lean_box(0);
x_224 = lean_name_mk_string(x_223, x_222);
x_225 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_218);
lean_ctor_set(x_225, 2, x_219);
lean_ctor_set(x_225, 3, x_220);
x_226 = l_Lean_MacroScopesView_review(x_225);
x_227 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_228 = 1;
lean_inc(x_2);
lean_inc(x_221);
x_229 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_5, x_227, x_228, x_221, x_2, x_13);
lean_dec(x_5);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
lean_inc(x_2);
x_231 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__1(x_12, x_2, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_272; lean_object* x_273; lean_object* x_283; lean_object* x_284; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_283 = lean_ctor_get(x_1, 1);
lean_inc(x_283);
lean_inc(x_2);
x_284 = l_Lean_Elab_Command_mkDeclName(x_283, x_226, x_2, x_232);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_313; lean_object* x_314; lean_object* x_315; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_313 = 2;
x_314 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_285);
x_315 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_285, x_313, x_287, x_314, x_2, x_286);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
lean_inc(x_2);
x_317 = l_Lean_Elab_Command_getLevelNames(x_2, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
lean_inc(x_285);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_285);
lean_inc(x_4);
lean_inc(x_285);
x_321 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 7, 4);
lean_closure_set(x_321, 0, x_1);
lean_closure_set(x_321, 1, x_285);
lean_closure_set(x_321, 2, x_318);
lean_closure_set(x_321, 3, x_4);
lean_inc(x_2);
x_322 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_319);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_323);
lean_dec(x_323);
lean_inc(x_2);
x_326 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_324);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_2, x_327, x_320);
x_330 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_327);
lean_dec(x_327);
x_331 = l_Lean_Elab_Term_elabBinders___rarg(x_325, x_321, x_329, x_330);
lean_dec(x_325);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
lean_inc(x_2);
x_334 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_328);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_ctor_get(x_335, 0);
lean_inc(x_338);
lean_dec(x_335);
x_339 = lean_ctor_get(x_333, 2);
lean_inc(x_339);
lean_dec(x_333);
x_340 = lean_ctor_get(x_336, 2);
lean_inc(x_340);
x_341 = lean_ctor_get(x_336, 3);
lean_inc(x_341);
x_342 = lean_ctor_get(x_336, 4);
lean_inc(x_342);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 lean_ctor_release(x_336, 4);
 x_343 = x_336;
} else {
 lean_dec_ref(x_336);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 5, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_338);
lean_ctor_set(x_344, 1, x_339);
lean_ctor_set(x_344, 2, x_340);
lean_ctor_set(x_344, 3, x_341);
lean_ctor_set(x_344, 4, x_342);
lean_inc(x_2);
x_345 = l___private_Init_Lean_Elab_Command_3__setState(x_344, x_2, x_337);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_288 = x_332;
x_289 = x_346;
goto block_312;
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_332);
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_dec(x_345);
x_272 = x_347;
x_273 = x_348;
goto block_282;
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_349 = lean_ctor_get(x_334, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_334, 1);
lean_inc(x_350);
lean_dec(x_334);
x_272 = x_349;
x_273 = x_350;
goto block_282;
}
}
else
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_331, 0);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_352 = lean_ctor_get(x_331, 1);
lean_inc(x_352);
lean_dec(x_331);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec(x_351);
lean_inc(x_2);
x_354 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_328);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_ctor_get(x_355, 0);
lean_inc(x_358);
lean_dec(x_355);
x_359 = lean_ctor_get(x_352, 2);
lean_inc(x_359);
lean_dec(x_352);
x_360 = lean_ctor_get(x_356, 2);
lean_inc(x_360);
x_361 = lean_ctor_get(x_356, 3);
lean_inc(x_361);
x_362 = lean_ctor_get(x_356, 4);
lean_inc(x_362);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 lean_ctor_release(x_356, 2);
 lean_ctor_release(x_356, 3);
 lean_ctor_release(x_356, 4);
 x_363 = x_356;
} else {
 lean_dec_ref(x_356);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_359);
lean_ctor_set(x_364, 2, x_360);
lean_ctor_set(x_364, 3, x_361);
lean_ctor_set(x_364, 4, x_362);
lean_inc(x_2);
x_365 = l___private_Init_Lean_Elab_Command_3__setState(x_364, x_2, x_357);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
lean_dec(x_365);
x_272 = x_353;
x_273 = x_366;
goto block_282;
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_353);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec(x_365);
x_272 = x_367;
x_273 = x_368;
goto block_282;
}
}
else
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_353);
lean_dec(x_352);
x_369 = lean_ctor_get(x_354, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_354, 1);
lean_inc(x_370);
lean_dec(x_354);
x_272 = x_369;
x_273 = x_370;
goto block_282;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_331);
x_371 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_372 = l_unreachable_x21___rarg(x_371);
lean_inc(x_2);
x_373 = lean_apply_2(x_372, x_2, x_328);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_288 = x_374;
x_289 = x_375;
goto block_312;
}
else
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_376 = lean_ctor_get(x_373, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_373, 1);
lean_inc(x_377);
lean_dec(x_373);
x_272 = x_376;
x_273 = x_377;
goto block_282;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_378 = lean_ctor_get(x_326, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_326, 1);
lean_inc(x_379);
lean_dec(x_326);
x_272 = x_378;
x_273 = x_379;
goto block_282;
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_380 = lean_ctor_get(x_322, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_322, 1);
lean_inc(x_381);
lean_dec(x_322);
x_272 = x_380;
x_273 = x_381;
goto block_282;
}
}
else
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
lean_dec(x_1);
x_382 = lean_ctor_get(x_317, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_317, 1);
lean_inc(x_383);
lean_dec(x_317);
x_272 = x_382;
x_273 = x_383;
goto block_282;
}
}
else
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
lean_dec(x_1);
x_384 = lean_ctor_get(x_315, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_315, 1);
lean_inc(x_385);
lean_dec(x_315);
x_272 = x_384;
x_273 = x_385;
goto block_282;
}
block_312:
{
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_290; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_4);
x_290 = lean_box(0);
x_233 = x_290;
x_234 = x_289;
goto block_271;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
lean_dec(x_288);
lean_inc(x_2);
x_292 = l_Lean_Elab_Command_addDecl(x_4, x_291, x_2, x_289);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_294 = 0;
x_295 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_285);
x_296 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_285, x_294, x_287, x_295, x_2, x_293);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
lean_inc(x_2);
x_298 = l_Lean_Elab_Command_compileDecl(x_4, x_291, x_2, x_297);
lean_dec(x_291);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = 1;
lean_inc(x_2);
x_301 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_285, x_300, x_287, x_295, x_2, x_299);
lean_dec(x_287);
lean_dec(x_4);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_233 = x_302;
x_234 = x_303;
goto block_271;
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_221);
x_304 = lean_ctor_get(x_301, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
lean_dec(x_301);
x_272 = x_304;
x_273 = x_305;
goto block_282;
}
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_306 = lean_ctor_get(x_298, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_298, 1);
lean_inc(x_307);
lean_dec(x_298);
x_272 = x_306;
x_273 = x_307;
goto block_282;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_291);
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_308 = lean_ctor_get(x_296, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_296, 1);
lean_inc(x_309);
lean_dec(x_296);
x_272 = x_308;
x_273 = x_309;
goto block_282;
}
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_291);
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_221);
lean_dec(x_4);
x_310 = lean_ctor_get(x_292, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_292, 1);
lean_inc(x_311);
lean_dec(x_292);
x_272 = x_310;
x_273 = x_311;
goto block_282;
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_283);
lean_dec(x_221);
lean_dec(x_4);
lean_dec(x_1);
x_386 = lean_ctor_get(x_284, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_284, 1);
lean_inc(x_387);
lean_dec(x_284);
x_272 = x_386;
x_273 = x_387;
goto block_282;
}
block_271:
{
lean_object* x_235; 
lean_inc(x_2);
lean_inc(x_10);
x_235 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__2(x_10, x_2, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_10);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
lean_inc(x_2);
x_237 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_238, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_238, 4);
lean_inc(x_244);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 lean_ctor_release(x_238, 4);
 x_245 = x_238;
} else {
 lean_dec_ref(x_238);
 x_245 = lean_box(0);
}
x_246 = l_Lean_Name_getNumParts___main(x_221);
lean_dec(x_221);
x_247 = l_List_drop___main___rarg(x_246, x_242);
lean_dec(x_242);
if (lean_is_scalar(x_245)) {
 x_248 = lean_alloc_ctor(0, 5, 0);
} else {
 x_248 = x_245;
}
lean_ctor_set(x_248, 0, x_240);
lean_ctor_set(x_248, 1, x_241);
lean_ctor_set(x_248, 2, x_247);
lean_ctor_set(x_248, 3, x_243);
lean_ctor_set(x_248, 4, x_244);
x_249 = l___private_Init_Lean_Elab_Command_3__setState(x_248, x_2, x_239);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_233);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_233);
x_253 = lean_ctor_get(x_249, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_255 = x_249;
} else {
 lean_dec_ref(x_249);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_233);
lean_dec(x_221);
lean_dec(x_2);
x_257 = lean_ctor_get(x_237, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_237, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_259 = x_237;
} else {
 lean_dec_ref(x_237);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_233);
lean_dec(x_221);
x_261 = lean_ctor_get(x_235, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_235, 1);
lean_inc(x_262);
lean_dec(x_235);
x_263 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__3(x_10, x_2, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
 lean_ctor_set_tag(x_266, 1);
}
lean_ctor_set(x_266, 0, x_261);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_261);
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_269 = x_263;
} else {
 lean_dec_ref(x_263);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
block_282:
{
lean_object* x_274; 
x_274 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__4(x_10, x_2, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_272);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_272);
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_388 = lean_ctor_get(x_231, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_231, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_390 = x_231;
} else {
 lean_dec_ref(x_231);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_392 = lean_ctor_get(x_229, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_229, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_394 = x_229;
} else {
 lean_dec_ref(x_229);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_396 = l_Lean_Elab_Command_withDeclId___closed__3;
x_397 = l_Lean_Elab_Command_throwError___rarg(x_5, x_396, x_2, x_13);
lean_dec(x_5);
return x_397;
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_414 = !lean_is_exclusive(x_9);
if (x_414 == 0)
{
return x_9;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_9, 0);
x_416 = lean_ctor_get(x_9, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_9);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabDefLike___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_Definition_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
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
lean_object* initialize_Init_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Init_Lean_Util_CollectFVars(lean_object*);
lean_object* initialize_Init_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Init_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Definition(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_removeUnused___closed__1 = _init_l_Lean_Elab_Command_removeUnused___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_removeUnused___closed__1);
l_Lean_Elab_Command_mkDef___lambda__1___closed__1 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__1);
l_Lean_Elab_Command_mkDef___lambda__1___closed__2 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__2);
l_Lean_Elab_Command_mkDef___lambda__1___closed__3 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__3);
l_Lean_Elab_Command_mkDef___lambda__1___closed__4 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__4);
l_Lean_Elab_Command_mkDef___lambda__1___closed__5 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__5);
l_Lean_Elab_Command_mkDef___lambda__1___closed__6 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__6);
l_Lean_Elab_Command_elabDefVal___closed__1 = _init_l_Lean_Elab_Command_elabDefVal___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__1);
l_Lean_Elab_Command_elabDefVal___closed__2 = _init_l_Lean_Elab_Command_elabDefVal___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__2);
l_Lean_Elab_Command_elabDefVal___closed__3 = _init_l_Lean_Elab_Command_elabDefVal___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__3);
res = l___private_Init_Lean_Elab_Definition_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
