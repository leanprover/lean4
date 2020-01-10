// Lean compiler output
// Module: Init.Lean.Elab.Definition
// Imports: Init.Lean.Util.CollectLevelParams Init.Lean.Util.CollectFVars Init.Lean.Elab.DeclModifiers Init.Lean.Elab.TermBinders
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
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_collectUsedFVarsAtFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabDefVal___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_20__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_collectUsedFVarsAtFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isExample(uint8_t);
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Command_removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l___private_Init_Lean_Elab_Term_14__resumePostponed___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_11__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen(lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
lean_object* l_Lean_Elab_Command_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withUsedWhen_x27(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_9__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isDefOrOpaque___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_collectUsedFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_14__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_removeUnused___closed__1;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
uint8_t l_Lean_Elab_Command_DefKind_isDefOrOpaque(uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_10__mkTermState(lean_object*);
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
x_2 = l_HashMap_Inhabited___closed__1;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_apply_3(x_7, x_18, x_8, x_15);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 2);
x_30 = lean_ctor_get(x_8, 3);
x_31 = lean_ctor_get(x_8, 4);
x_32 = lean_ctor_get(x_8, 5);
x_33 = lean_ctor_get(x_8, 6);
x_34 = lean_ctor_get(x_8, 7);
x_35 = lean_ctor_get(x_8, 8);
x_36 = lean_ctor_get(x_8, 9);
x_37 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_39 = x_14;
} else {
 lean_dec_ref(x_14);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 3, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_17);
x_41 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
lean_ctor_set(x_41, 2, x_29);
lean_ctor_set(x_41, 3, x_30);
lean_ctor_set(x_41, 4, x_31);
lean_ctor_set(x_41, 5, x_32);
lean_ctor_set(x_41, 6, x_33);
lean_ctor_set(x_41, 7, x_34);
lean_ctor_set(x_41, 8, x_35);
lean_ctor_set(x_41, 9, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_37);
x_42 = lean_apply_3(x_7, x_18, x_41, x_15);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
x_1 = l_HashMap_Inhabited___closed__1;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
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
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_32);
x_39 = l_Lean_CollectLevelParams_main___main(x_32, x_38);
lean_inc(x_36);
x_40 = l_Lean_CollectLevelParams_main___main(x_36, x_39);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Command_sortDeclLevelParams(x_6, x_41);
switch (x_7) {
case 0:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_32);
x_44 = lean_ctor_get(x_9, 1);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*2 + 3);
x_46 = l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_34, 0, x_49);
return x_34;
}
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_11);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_32);
x_51 = lean_task_pure(x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_34, 0, x_54);
return x_34;
}
case 2:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_42);
lean_free_object(x_34);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_8);
x_55 = l___private_Init_Lean_Elab_Term_14__resumePostponed___lambda__1___closed__1;
x_56 = l_unreachable_x21___rarg(x_55);
x_57 = lean_apply_2(x_56, x_11, x_37);
return x_57;
}
default: 
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_11);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 2, x_32);
x_59 = lean_ctor_get(x_9, 1);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*2 + 3);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_36);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_60);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_34, 0, x_63);
return x_34;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_34, 0);
x_65 = lean_ctor_get(x_34, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_34);
x_66 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_32);
x_67 = l_Lean_CollectLevelParams_main___main(x_32, x_66);
lean_inc(x_64);
x_68 = l_Lean_CollectLevelParams_main___main(x_64, x_67);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Elab_Command_sortDeclLevelParams(x_6, x_69);
switch (x_7) {
case 0:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_11);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_8);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_32);
x_72 = lean_ctor_get(x_9, 1);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*2 + 3);
x_74 = l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
return x_78;
}
case 1:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_11);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_32);
x_80 = lean_task_pure(x_64);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_65);
return x_84;
}
case 2:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_70);
lean_dec(x_64);
lean_dec(x_32);
lean_dec(x_8);
x_85 = l___private_Init_Lean_Elab_Term_14__resumePostponed___lambda__1___closed__1;
x_86 = l_unreachable_x21___rarg(x_85);
x_87 = lean_apply_2(x_86, x_11, x_65);
return x_87;
}
default: 
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_11);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_8);
lean_ctor_set(x_88, 1, x_70);
lean_ctor_set(x_88, 2, x_32);
x_89 = lean_ctor_get(x_9, 1);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*2 + 3);
x_91 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_64);
lean_ctor_set_uint8(x_91, sizeof(void*)*2, x_90);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_65);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_99 = !lean_is_exclusive(x_19);
if (x_99 == 0)
{
return x_19;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_19, 0);
x_101 = lean_ctor_get(x_19, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_19);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_16);
if (x_103 == 0)
{
return x_16;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_16, 0);
x_105 = lean_ctor_get(x_16, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_16);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_13);
if (x_107 == 0)
{
return x_13;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_13, 0);
x_109 = lean_ctor_get(x_13, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_13);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
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
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_8);
x_13 = l___private_Init_Lean_Elab_Term_20__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
x_15 = l_Lean_Elab_Term_instantiateMVars(x_10, x_6, x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
lean_inc(x_8);
x_19 = l_Lean_Elab_Term_instantiateMVars(x_18, x_7, x_8, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_20);
x_22 = l_Lean_Elab_Term_inferType(x_18, x_20, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_16);
lean_inc(x_8);
lean_inc(x_10);
x_26 = l_Lean_Elab_Term_ensureHasType(x_10, x_25, x_23, x_20, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
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
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_10);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 12, 9);
lean_closure_set(x_34, 0, x_10);
lean_closure_set(x_34, 1, x_5);
lean_closure_set(x_34, 2, x_16);
lean_closure_set(x_34, 3, x_28);
lean_closure_set(x_34, 4, x_18);
lean_closure_set(x_34, 5, x_3);
lean_closure_set(x_34, 6, x_33);
lean_closure_set(x_34, 7, x_2);
lean_closure_set(x_34, 8, x_1);
x_35 = l_Lean_Elab_Command_withUsedWhen___rarg(x_10, x_4, x_5, x_28, x_16, x_32, x_34, x_8, x_29);
lean_dec(x_5);
lean_dec(x_10);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_16);
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
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_10);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 12, 9);
lean_closure_set(x_43, 0, x_10);
lean_closure_set(x_43, 1, x_5);
lean_closure_set(x_43, 2, x_16);
lean_closure_set(x_43, 3, x_37);
lean_closure_set(x_43, 4, x_18);
lean_closure_set(x_43, 5, x_3);
lean_closure_set(x_43, 6, x_42);
lean_closure_set(x_43, 7, x_2);
lean_closure_set(x_43, 8, x_1);
x_44 = l_Lean_Elab_Command_withUsedWhen___rarg(x_10, x_4, x_5, x_37, x_16, x_41, x_43, x_8, x_38);
lean_dec(x_5);
lean_dec(x_10);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_18);
lean_dec(x_16);
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
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_17 = l_Lean_Elab_Term_elabTerm(x_14, x_15, x_16, x_16, x_3, x_4);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
x_31 = l___private_Init_Lean_Elab_Term_20__synthesizeSyntheticMVarsAux___main(x_29, x_30, x_8, x_28);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getIdAt(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_5, x_8);
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_getLevelNames(x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_207; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_207 = l_Lean_Syntax_isNone(x_9);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_209 = l_Lean_Syntax_getArgs(x_208);
lean_dec(x_208);
x_210 = lean_unsigned_to_nat(2u);
x_211 = l_Array_empty___closed__1;
x_212 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_210, x_209, x_6, x_211);
lean_dec(x_209);
lean_inc(x_2);
lean_inc(x_11);
x_213 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabDefLike___spec__5(x_1, x_212, x_6, x_11, x_2, x_12);
lean_dec(x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_13 = x_214;
x_14 = x_215;
goto block_206;
}
else
{
uint8_t x_216; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_213);
if (x_216 == 0)
{
return x_213;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_213, 0);
x_218 = lean_ctor_get(x_213, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_213);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_dec(x_9);
lean_inc(x_11);
x_13 = x_11;
x_14 = x_12;
goto block_206;
}
block_206:
{
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_18 = 1;
lean_inc(x_2);
lean_inc(x_15);
x_19 = l___private_Init_Lean_Elab_Command_14__addScopes___main(x_5, x_17, x_18, x_15, x_2, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_2);
x_21 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__1(x_13, x_2, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_76; lean_object* x_77; lean_object* x_88; lean_object* x_89; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_name_mk_string(x_23, x_16);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
lean_inc(x_2);
x_89 = l_Lean_Elab_Command_mkDeclName(x_88, x_24, x_2, x_22);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_117; lean_object* x_118; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_117 = 2;
lean_inc(x_2);
lean_inc(x_90);
x_118 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_90, x_117, x_92, x_6, x_2, x_91);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_2);
x_120 = l_Lean_Elab_Command_getLevelNames(x_2, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_90);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_90);
lean_inc(x_4);
lean_inc(x_90);
x_124 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 7, 4);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_90);
lean_closure_set(x_124, 2, x_121);
lean_closure_set(x_124, 3, x_4);
lean_inc(x_2);
x_125 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l___private_Init_Lean_Elab_Command_11__getVarDecls(x_126);
x_129 = l___private_Init_Lean_Elab_Command_9__mkTermContext(x_2, x_126, x_123);
x_130 = l___private_Init_Lean_Elab_Command_10__mkTermState(x_126);
lean_dec(x_126);
x_131 = l_Lean_Elab_Term_elabBinders___rarg(x_128, x_124, x_129, x_130);
lean_dec(x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_2);
x_134 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_127);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_133, 2);
lean_inc(x_139);
lean_dec(x_133);
x_140 = !lean_is_exclusive(x_136);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_136, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_136, 0);
lean_dec(x_142);
lean_ctor_set(x_136, 1, x_139);
lean_ctor_set(x_136, 0, x_138);
lean_inc(x_2);
x_143 = l___private_Init_Lean_Elab_Command_3__setState(x_136, x_2, x_137);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_93 = x_132;
x_94 = x_144;
goto block_116;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_132);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_76 = x_145;
x_77 = x_146;
goto block_87;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_136, 2);
x_148 = lean_ctor_get(x_136, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_136);
x_149 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_139);
lean_ctor_set(x_149, 2, x_147);
lean_ctor_set(x_149, 3, x_148);
lean_inc(x_2);
x_150 = l___private_Init_Lean_Elab_Command_3__setState(x_149, x_2, x_137);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_93 = x_132;
x_94 = x_151;
goto block_116;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_132);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_76 = x_152;
x_77 = x_153;
goto block_87;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_154 = lean_ctor_get(x_134, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_76 = x_154;
x_77 = x_155;
goto block_87;
}
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_131, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_157 = lean_ctor_get(x_131, 1);
lean_inc(x_157);
lean_dec(x_131);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_2);
x_159 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_127);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_ctor_get(x_157, 2);
lean_inc(x_164);
lean_dec(x_157);
x_165 = !lean_is_exclusive(x_161);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_161, 1);
lean_dec(x_166);
x_167 = lean_ctor_get(x_161, 0);
lean_dec(x_167);
lean_ctor_set(x_161, 1, x_164);
lean_ctor_set(x_161, 0, x_163);
lean_inc(x_2);
x_168 = l___private_Init_Lean_Elab_Command_3__setState(x_161, x_2, x_162);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_76 = x_158;
x_77 = x_169;
goto block_87;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_158);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_76 = x_170;
x_77 = x_171;
goto block_87;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_161, 2);
x_173 = lean_ctor_get(x_161, 3);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_161);
x_174 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_174, 0, x_163);
lean_ctor_set(x_174, 1, x_164);
lean_ctor_set(x_174, 2, x_172);
lean_ctor_set(x_174, 3, x_173);
lean_inc(x_2);
x_175 = l___private_Init_Lean_Elab_Command_3__setState(x_174, x_2, x_162);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_76 = x_158;
x_77 = x_176;
goto block_87;
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_158);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_76 = x_177;
x_77 = x_178;
goto block_87;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_158);
lean_dec(x_157);
x_179 = lean_ctor_get(x_159, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_159, 1);
lean_inc(x_180);
lean_dec(x_159);
x_76 = x_179;
x_77 = x_180;
goto block_87;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_131);
x_181 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_182 = l_unreachable_x21___rarg(x_181);
lean_inc(x_2);
x_183 = lean_apply_2(x_182, x_2, x_127);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_93 = x_184;
x_94 = x_185;
goto block_116;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
x_76 = x_186;
x_77 = x_187;
goto block_87;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_188 = lean_ctor_get(x_125, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_125, 1);
lean_inc(x_189);
lean_dec(x_125);
x_76 = x_188;
x_77 = x_189;
goto block_87;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_190 = lean_ctor_get(x_120, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_120, 1);
lean_inc(x_191);
lean_dec(x_120);
x_76 = x_190;
x_77 = x_191;
goto block_87;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_192 = lean_ctor_get(x_118, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_118, 1);
lean_inc(x_193);
lean_dec(x_118);
x_76 = x_192;
x_77 = x_193;
goto block_87;
}
block_116:
{
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_4);
x_95 = lean_box(0);
x_25 = x_95;
x_26 = x_94;
goto block_75;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_2);
lean_inc(x_4);
x_97 = l_Lean_Elab_Command_addDecl(x_4, x_96, x_2, x_94);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = 0;
lean_inc(x_2);
lean_inc(x_90);
x_100 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_90, x_99, x_92, x_6, x_2, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_2);
lean_inc(x_4);
x_102 = l_Lean_Elab_Command_compileDecl(x_4, x_96, x_2, x_101);
lean_dec(x_96);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = 1;
lean_inc(x_2);
x_105 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_4, x_90, x_104, x_92, x_6, x_2, x_103);
lean_dec(x_92);
lean_dec(x_4);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_25 = x_106;
x_26 = x_107;
goto block_75;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_15);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_76 = x_108;
x_77 = x_109;
goto block_87;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_dec(x_102);
x_76 = x_110;
x_77 = x_111;
goto block_87;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_96);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
lean_dec(x_100);
x_76 = x_112;
x_77 = x_113;
goto block_87;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_96);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_4);
x_114 = lean_ctor_get(x_97, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_97, 1);
lean_inc(x_115);
lean_dec(x_97);
x_76 = x_114;
x_77 = x_115;
goto block_87;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_88);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_194 = lean_ctor_get(x_89, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_89, 1);
lean_inc(x_195);
lean_dec(x_89);
x_76 = x_194;
x_77 = x_195;
goto block_87;
}
block_75:
{
lean_object* x_27; 
lean_inc(x_2);
lean_inc(x_11);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__2(x_11, x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_2);
x_29 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 2);
x_34 = l_Lean_Name_getNumParts___main(x_15);
lean_dec(x_15);
x_35 = l_List_drop___main___rarg(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_30, 2, x_35);
x_36 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_31);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_25);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_25);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
x_47 = lean_ctor_get(x_30, 2);
x_48 = lean_ctor_get(x_30, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_49 = l_Lean_Name_getNumParts___main(x_15);
lean_dec(x_15);
x_50 = l_List_drop___main___rarg(x_49, x_47);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_48);
x_52 = l___private_Init_Lean_Elab_Command_3__setState(x_51, x_2, x_31);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_25);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_29);
if (x_60 == 0)
{
return x_29;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_29);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_25);
lean_dec(x_15);
x_64 = lean_ctor_get(x_27, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_27, 1);
lean_inc(x_65);
lean_dec(x_27);
x_66 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__3(x_11, x_2, x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_64);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
block_87:
{
lean_object* x_78; 
x_78 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabDefLike___spec__4(x_11, x_2, x_77);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_76);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_78, 0);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_78);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_21);
if (x_196 == 0)
{
return x_21;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_21, 0);
x_198 = lean_ctor_get(x_21, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_21);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_19);
if (x_200 == 0)
{
return x_19;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_19, 0);
x_202 = lean_ctor_get(x_19, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_19);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_204 = l_Lean_Elab_Command_withDeclId___closed__3;
x_205 = l_Lean_Elab_Command_throwError___rarg(x_5, x_204, x_2, x_14);
return x_205;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_10);
if (x_220 == 0)
{
return x_10;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_10, 0);
x_222 = lean_ctor_get(x_10, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_10);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
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
lean_object* initialize_Init_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Init_Lean_Util_CollectFVars(lean_object*);
lean_object* initialize_Init_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Init_Lean_Elab_TermBinders(lean_object*);
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
res = initialize_Init_Lean_Elab_TermBinders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_removeUnused___closed__1 = _init_l_Lean_Elab_Command_removeUnused___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_removeUnused___closed__1);
l_Lean_Elab_Command_mkDef___lambda__1___closed__1 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__1);
l_Lean_Elab_Command_mkDef___lambda__1___closed__2 = _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDef___lambda__1___closed__2);
l_Lean_Elab_Command_elabDefVal___closed__1 = _init_l_Lean_Elab_Command_elabDefVal___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__1);
l_Lean_Elab_Command_elabDefVal___closed__2 = _init_l_Lean_Elab_Command_elabDefVal___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__2);
l_Lean_Elab_Command_elabDefVal___closed__3 = _init_l_Lean_Elab_Command_elabDefVal___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDefVal___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
