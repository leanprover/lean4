// Lean compiler output
// Module: Lean.Elab.Definition
// Imports: Init Std.ShareCommon Lean.Util.CollectLevelParams Lean.Util.FoldConsts Lean.Elab.CollectFVars Lean.Elab.DeclModifiers Lean.Elab.Binders
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1;
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen(lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabDefLike___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabDefLike___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isExample(uint8_t);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isTheorem___boxed(lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(uint8_t);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
lean_object* l_Lean_mkFreshTypeMVar___at___private_Lean_Elab_Term_11__exceptionToSorry___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__3;
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_1__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabDefLike___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__6;
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_object* l___private_Lean_Elab_Definition_4__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_Command_4__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_Command_Lean_MonadOptions___spec__1(lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27(lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
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
uint8_t l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(uint8_t x_1) {
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
lean_object* l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(x_2);
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
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Elab_Term_collectUsedFVars(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_collectUsedFVars(x_14, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(x_2, x_2, x_19, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_removeUnused(x_1, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Definition_1__removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
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
x_23 = l_Lean_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(x_19, x_20, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
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
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__1() {
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
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("body");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_9, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l_Lean_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_1, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_26 = l_Lean_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_9, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Elab_Term_levelMVarToParam(x_21, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_35 = l_Lean_Elab_Term_levelMVarToParam(x_27, x_34, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_33, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
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
x_121 = lean_ctor_get(x_14, 0);
lean_inc(x_121);
x_122 = l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
x_123 = l_Lean_checkTraceOption(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
x_52 = x_44;
goto block_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_inc(x_7);
x_124 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_124, 0, x_7);
x_125 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_126 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_48);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_48);
x_128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Command_mkDef___lambda__1___closed__6;
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_MessageData_ofList___closed__3;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_51);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_51);
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_135 = l_Lean_Elab_Term_logTrace(x_122, x_134, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_52 = x_136;
goto block_120;
}
else
{
uint8_t x_137; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_135);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
block_120:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
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
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
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
x_95 = lean_task_pure(x_51);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (lean_is_scalar(x_45)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_45;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_52);
return x_99;
}
case 2:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_57);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_7);
x_100 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_101 = l_unreachable_x21___rarg(x_100);
x_102 = lean_apply_7(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_52);
return x_102;
}
case 3:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_103 = lean_ctor_get(x_57, 0);
lean_inc(x_103);
lean_dec(x_57);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_7);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_48);
x_105 = lean_ctor_get(x_8, 1);
x_106 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 3);
x_107 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_51);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_106);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_45)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_45;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_52);
return x_110;
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_111 = lean_ctor_get(x_57, 0);
lean_inc(x_111);
lean_dec(x_57);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_7);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_48);
x_113 = lean_ctor_get(x_8, 1);
x_114 = lean_ctor_get_uint8(x_113, sizeof(void*)*2 + 3);
x_115 = lean_box(1);
x_116 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_51);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*3, x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_45)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_45;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_52);
return x_119;
}
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_141 = !lean_is_exclusive(x_42);
if (x_141 == 0)
{
return x_42;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_42, 0);
x_143 = lean_ctor_get(x_42, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_42);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_145 = !lean_is_exclusive(x_39);
if (x_145 == 0)
{
return x_39;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_39, 0);
x_147 = lean_ctor_get(x_39, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_39);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_35);
if (x_149 == 0)
{
return x_35;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_35, 0);
x_151 = lean_ctor_get(x_35, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_35);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_153 = !lean_is_exclusive(x_30);
if (x_153 == 0)
{
return x_30;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_30, 0);
x_155 = lean_ctor_get(x_30, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_30);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
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
x_157 = !lean_is_exclusive(x_26);
if (x_157 == 0)
{
return x_26;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_26, 0);
x_159 = lean_ctor_get(x_26, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_26);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
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
x_161 = !lean_is_exclusive(x_23);
if (x_161 == 0)
{
return x_23;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_23, 0);
x_163 = lean_ctor_get(x_23, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_23);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
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
x_165 = !lean_is_exclusive(x_20);
if (x_165 == 0)
{
return x_20;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_20, 0);
x_167 = lean_ctor_get(x_20, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_20);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
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
x_169 = !lean_is_exclusive(x_17);
if (x_169 == 0)
{
return x_17;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_17, 0);
x_171 = lean_ctor_get(x_17, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_17);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_inc(x_10);
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
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_41 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_44 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_36, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_49 = l_Lean_Elab_Command_DefKind_isExample(x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_44);
x_50 = l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(x_48);
x_51 = lean_box(x_48);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_6);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 16, 8);
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
x_58 = l_Lean_Elab_Command_DefKind_isExample(x_57);
if (x_58 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(x_57);
x_60 = lean_box(x_57);
lean_inc(x_55);
lean_inc(x_42);
lean_inc(x_6);
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 16, 8);
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
x_65 = !lean_is_exclusive(x_44);
if (x_65 == 0)
{
return x_44;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_44, 0);
x_67 = lean_ctor_get(x_44, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_44);
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
lean_dec(x_36);
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
x_69 = !lean_is_exclusive(x_41);
if (x_69 == 0)
{
return x_41;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_41, 0);
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_41);
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
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
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
x_77 = !lean_is_exclusive(x_35);
if (x_77 == 0)
{
return x_35;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_35, 0);
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_35);
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
x_81 = !lean_is_exclusive(x_27);
if (x_81 == 0)
{
return x_27;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_27, 0);
x_83 = lean_ctor_get(x_27, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_27);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get(x_13, 0);
x_86 = lean_ctor_get(x_13, 1);
x_87 = lean_ctor_get(x_13, 2);
x_88 = lean_ctor_get(x_13, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_13);
x_89 = l_Lean_replaceRef(x_16, x_88);
lean_dec(x_16);
x_90 = l_Lean_replaceRef(x_89, x_88);
lean_dec(x_89);
x_91 = l_Lean_replaceRef(x_90, x_88);
lean_dec(x_88);
lean_dec(x_90);
lean_inc(x_91);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_86);
lean_ctor_set(x_92, 2, x_87);
lean_ctor_set(x_92, 3, x_91);
x_93 = 1;
x_94 = lean_box(0);
lean_inc(x_14);
lean_inc(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_95 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_93, x_94, x_9, x_10, x_11, x_12, x_92, x_14, x_15);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_1, 5);
lean_inc(x_97);
lean_inc(x_7);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_7);
x_99 = l_Lean_replaceRef(x_97, x_91);
lean_dec(x_97);
x_100 = l_Lean_replaceRef(x_99, x_91);
lean_dec(x_99);
x_101 = l_Lean_replaceRef(x_100, x_91);
lean_dec(x_91);
lean_dec(x_100);
x_102 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_102, 0, x_85);
lean_ctor_set(x_102, 1, x_86);
lean_ctor_set(x_102, 2, x_87);
lean_ctor_set(x_102, 3, x_101);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_103 = l_Lean_Elab_Term_ensureHasType(x_98, x_8, x_9, x_10, x_11, x_12, x_102, x_14, x_96);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = 0;
lean_inc(x_14);
lean_inc(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_107 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_106, x_94, x_9, x_10, x_11, x_12, x_92, x_14, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_14);
lean_inc(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_109 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_7, x_9, x_10, x_11, x_12, x_92, x_14, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_14);
lean_inc(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_112 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_104, x_9, x_10, x_11, x_12, x_92, x_14, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_117 = l_Lean_Elab_Command_DefKind_isExample(x_116);
if (x_117 == 0)
{
uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_115);
x_118 = l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(x_116);
x_119 = lean_box(x_116);
lean_inc(x_113);
lean_inc(x_110);
lean_inc(x_6);
x_120 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 16, 8);
lean_closure_set(x_120, 0, x_6);
lean_closure_set(x_120, 1, x_110);
lean_closure_set(x_120, 2, x_113);
lean_closure_set(x_120, 3, x_3);
lean_closure_set(x_120, 4, x_4);
lean_closure_set(x_120, 5, x_119);
lean_closure_set(x_120, 6, x_2);
lean_closure_set(x_120, 7, x_1);
x_121 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_113, x_110, x_118, x_120, x_9, x_10, x_11, x_12, x_92, x_14, x_114);
lean_dec(x_6);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_113);
lean_dec(x_110);
lean_dec(x_92);
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
x_122 = lean_box(0);
if (lean_is_scalar(x_115)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_115;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_114);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_110);
lean_dec(x_92);
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
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_126 = x_112;
} else {
 lean_dec_ref(x_112);
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
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_104);
lean_dec(x_92);
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
x_128 = lean_ctor_get(x_109, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_109, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_130 = x_109;
} else {
 lean_dec_ref(x_109);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_104);
lean_dec(x_92);
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
x_132 = lean_ctor_get(x_107, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_107, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_134 = x_107;
} else {
 lean_dec_ref(x_107);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_92);
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
x_136 = lean_ctor_get(x_103, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_103, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_138 = x_103;
} else {
 lean_dec_ref(x_103);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
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
x_140 = lean_ctor_get(x_95, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_95, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_142 = x_95;
} else {
 lean_dec_ref(x_95);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Elab_Command_mkDef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
return x_18;
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
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_Syntax_getKind(x_1);
x_11 = l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
x_12 = lean_name_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_13 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
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
x_16 = l_Lean_Elab_Command_elabDefVal___closed__3;
x_17 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__2___rarg(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_List_head_x21___at_Lean_Elab_Command_Lean_MonadOptions___spec__1(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_KernelException_toMessageData(x_1, x_10);
x_12 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_11, x_2, x_3, x_7);
return x_12;
}
}
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabDefLike___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_add_decl(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2(x_10, x_2, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_12, x_2, x_3, x_7);
lean_dec(x_2);
return x_13;
}
}
}
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabDefLike___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_head_x21___at_Lean_Elab_Command_Lean_MonadOptions___spec__1(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_compile_decl(x_8, x_14, x_1);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2(x_16, x_2, x_3, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_18, x_2, x_3, x_11);
lean_dec(x_2);
return x_19;
}
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
x_19 = l_Lean_Elab_Command_mkDef(x_1, x_3, x_4, x_5, x_7, x_6, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
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
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 3);
lean_inc(x_19);
x_20 = l_Lean_replaceRef(x_2, x_19);
x_21 = l_Lean_replaceRef(x_20, x_19);
lean_dec(x_20);
x_22 = l_Lean_replaceRef(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_22);
x_24 = 0;
x_25 = lean_box(0);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_mkFreshTypeMVar___at___private_Lean_Elab_Term_11__exceptionToSorry___spec__1(x_24, x_25, x_8, x_9, x_10, x_11, x_23, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_1, 5);
lean_inc(x_29);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_27);
x_30 = l_Lean_Elab_Command_elabDefVal(x_29, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Command_mkDef(x_1, x_3, x_4, x_5, x_6, x_7, x_27, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_27);
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
lean_dec(x_1);
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
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_43 = l_Lean_Elab_Term_elabType(x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = 0;
x_47 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_46, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_instantiateMVars___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_54 = l_Lean_Elab_Command_DefKind_isTheorem(x_53);
lean_inc(x_7);
lean_inc(x_51);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__1), 14, 6);
lean_closure_set(x_55, 0, x_1);
lean_closure_set(x_55, 1, x_51);
lean_closure_set(x_55, 2, x_3);
lean_closure_set(x_55, 3, x_4);
lean_closure_set(x_55, 4, x_5);
lean_closure_set(x_55, 5, x_7);
x_56 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(x_6, x_7, x_51, x_54, x_55, x_8, x_9, x_10, x_11, x_12, x_13, x_52);
lean_dec(x_7);
return x_56;
}
else
{
uint8_t x_57; 
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
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_44);
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
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
return x_48;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
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
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_43);
if (x_65 == 0)
{
return x_43;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_43, 0);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_43);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = l_Lean_Syntax_getArgs(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__2___boxed), 14, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_5);
x_16 = l_Lean_Elab_Term_elabBinders___rarg(x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_Elab_Command_getRef(x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_replaceRef(x_2, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 5);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_12);
x_20 = l_Lean_Elab_Command_mkDeclName(x_8, x_4, x_19, x_6, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = 2;
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_21);
x_26 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_21, x_24, x_23, x_25, x_5, x_6, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_Command_getLevelNames___rarg(x_6, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_21);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_21);
lean_inc(x_21);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 12, 4);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_21);
lean_closure_set(x_32, 2, x_3);
lean_closure_set(x_32, 3, x_29);
x_33 = lean_st_ref_get(x_6, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_Command_4__getVarDecls(x_34);
lean_dec(x_34);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_32);
x_38 = l_Lean_Elab_Command_liftTermElabM___rarg(x_31, x_37, x_5, x_6, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
lean_inc(x_5);
x_48 = l_Lean_addDecl___at_Lean_Elab_Command_elabDefLike___spec__1(x_47, x_5, x_6, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = 0;
lean_inc(x_5);
lean_inc(x_21);
x_51 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_21, x_50, x_23, x_25, x_5, x_6, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_5);
x_53 = l_Lean_compileDecl___at_Lean_Elab_Command_elabDefLike___spec__3(x_47, x_5, x_6, x_52);
lean_dec(x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = 1;
x_56 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_21, x_55, x_23, x_25, x_5, x_6, x_54);
lean_dec(x_23);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_47);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_47);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
return x_48;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_48);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_38);
if (x_69 == 0)
{
return x_38;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_38, 0);
x_71 = lean_ctor_get(x_38, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
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
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_26);
if (x_73 == 0)
{
return x_26;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_26, 0);
x_75 = lean_ctor_get(x_26, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_26);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_20);
if (x_77 == 0)
{
return x_20;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_20, 0);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_20);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
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
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__4___boxed), 7, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_13);
x_17 = l_Lean_Elab_Command_withDeclId___rarg(x_15, x_16, x_2, x_3, x_14);
lean_dec(x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_24, 6, x_9);
x_25 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__4___boxed), 7, 3);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_26);
x_30 = l_Lean_Elab_Command_withDeclId___rarg(x_28, x_29, x_24, x_3, x_27);
lean_dec(x_28);
return x_30;
}
}
}
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at_Lean_Elab_Command_elabDefLike___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabDefLike___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addDecl___at_Lean_Elab_Command_elabDefLike___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabDefLike___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDecl___at_Lean_Elab_Command_elabDefLike___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabDefLike___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabDefLike___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Definition_4__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
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
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Definition(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
res = initialize_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Definition_1__removeUnused___closed__1 = _init_l___private_Lean_Elab_Definition_1__removeUnused___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Definition_1__removeUnused___closed__1);
l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1 = _init_l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1);
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
res = l___private_Lean_Elab_Definition_4__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
