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
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1;
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__2;
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l_Lean_Elab_Command_compileDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen(lean_object*);
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__1;
lean_object* l_Lean_Elab_Command_elabDefVal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isExample(uint8_t);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DepElim_getUnusedLevelParam___closed__1;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_DefKind_isTheorem___boxed(lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(uint8_t);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefVal___closed__3;
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_1__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_object* l___private_Lean_Elab_Definition_4__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_Command_8__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Command_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27(lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Definition_1__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_inc(x_5);
x_8 = l_Lean_Elab_Term_collectUsedFVars(x_7, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_collectUsedFVars(x_9, x_3, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_15 = l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(x_2, x_2, x_14, x_12, x_5, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_removeUnused(x_1, x_16, x_5, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
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
}
lean_object* l___private_Lean_Elab_Definition_1__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Definition_1__removeUnused(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_5 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_apply_3(x_6, x_1, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l___private_Lean_Elab_Definition_1__removeUnused(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_dec(x_22);
lean_ctor_set(x_13, 2, x_16);
lean_ctor_set(x_13, 1, x_15);
x_23 = lean_apply_3(x_6, x_17, x_7, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 3);
x_26 = lean_ctor_get(x_13, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_7, 0, x_27);
x_28 = lean_apply_3(x_6, x_17, x_7, x_14);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_7, 1);
x_30 = lean_ctor_get(x_7, 2);
x_31 = lean_ctor_get(x_7, 3);
x_32 = lean_ctor_get(x_7, 4);
x_33 = lean_ctor_get(x_7, 5);
x_34 = lean_ctor_get(x_7, 6);
x_35 = lean_ctor_get(x_7, 7);
x_36 = lean_ctor_get(x_7, 8);
x_37 = lean_ctor_get_uint8(x_7, sizeof(void*)*10);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 1);
x_39 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 2);
x_40 = lean_ctor_get(x_7, 9);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 4);
lean_inc(x_43);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 x_44 = x_13;
} else {
 lean_dec_ref(x_13);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_15);
lean_ctor_set(x_45, 2, x_16);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
x_46 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_29);
lean_ctor_set(x_46, 2, x_30);
lean_ctor_set(x_46, 3, x_31);
lean_ctor_set(x_46, 4, x_32);
lean_ctor_set(x_46, 5, x_33);
lean_ctor_set(x_46, 6, x_34);
lean_ctor_set(x_46, 7, x_35);
lean_ctor_set(x_46, 8, x_36);
lean_ctor_set(x_46, 9, x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*10, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 1, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 2, x_39);
x_47 = lean_apply_3(x_6, x_17, x_46, x_14);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_10);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Definition_2__withUsedWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
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
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___closed__1;
x_9 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_1, x_2, x_3, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("body");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkDef___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Elab_Term_mkForall(x_9, x_13, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
x_18 = l_Lean_Elab_Term_mkLambda(x_1, x_3, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
x_21 = l_Lean_Elab_Term_mkLambda(x_9, x_19, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_25 = l_Lean_Elab_Term_levelMVarToParam(x_16, x_24, x_10, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_10);
x_30 = l_Lean_Elab_Term_levelMVarToParam(x_22, x_29, x_10, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_10);
x_34 = l_Lean_Elab_Term_instantiateMVars(x_28, x_10, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_10);
x_37 = l_Lean_Elab_Term_instantiateMVars(x_33, x_10, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l_Std_ShareCommon_State_empty;
x_42 = lean_state_sharecommon(x_41, x_35);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_state_sharecommon(x_44, x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Meta_DepElim_getUnusedLevelParam___closed__1;
lean_inc(x_43);
x_48 = l_Lean_CollectLevelParams_main___main(x_43, x_47);
lean_inc(x_46);
x_49 = l_Lean_CollectLevelParams_main___main(x_46, x_48);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Elab_Command_sortDeclLevelParams(x_4, x_5, x_50);
x_114 = l_Lean_Elab_Term_getOptions(x_10, x_39);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Elab_Command_mkDef___lambda__1___closed__4;
x_118 = l_Lean_checkTraceOption(x_115, x_117);
lean_dec(x_115);
if (x_118 == 0)
{
x_52 = x_116;
goto block_113;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_7);
x_119 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_119, 0, x_7);
x_120 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_121 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
lean_inc(x_43);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_43);
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_MessageData_ofList___closed__3;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_inc(x_46);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_46);
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Elab_Term_logTrace(x_117, x_129, x_10, x_116);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_52 = x_131;
goto block_113;
}
block_113:
{
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_7);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Elab_Term_throwError___rarg(x_55, x_10, x_52);
return x_56;
}
else
{
switch (x_6) {
case 0:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_10);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_Lean_Elab_Term_getEnv___rarg(x_52);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; uint32_t x_64; uint32_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_7);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_43);
lean_inc(x_46);
x_62 = l_Lean_getMaxHeight(x_60, x_46);
x_63 = lean_unbox_uint32(x_62);
lean_dec(x_62);
x_64 = 1;
x_65 = x_63 + x_64;
x_66 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_66, 0, x_65);
x_67 = lean_ctor_get(x_8, 1);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*2 + 3);
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_46);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_58, 0, x_71);
return x_58;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint32_t x_76; uint32_t x_77; uint32_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_58, 0);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_58);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_7);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_43);
lean_inc(x_46);
x_75 = l_Lean_getMaxHeight(x_72, x_46);
x_76 = lean_unbox_uint32(x_75);
lean_dec(x_75);
x_77 = 1;
x_78 = x_76 + x_77;
x_79 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_79, 0, x_78);
x_80 = lean_ctor_get(x_8, 1);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*2 + 3);
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_46);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_73);
return x_85;
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
x_86 = lean_ctor_get(x_51, 0);
lean_inc(x_86);
lean_dec(x_51);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_7);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_43);
x_88 = lean_task_pure(x_46);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_40)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_40;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_52);
return x_92;
}
case 2:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_7);
x_93 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_94 = l_unreachable_x21___rarg(x_93);
x_95 = lean_apply_2(x_94, x_10, x_52);
return x_95;
}
case 3:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
x_96 = lean_ctor_get(x_51, 0);
lean_inc(x_96);
lean_dec(x_51);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_7);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_43);
x_98 = lean_ctor_get(x_8, 1);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*2 + 3);
x_100 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_46);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_99);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_40)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_40;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_52);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_10);
x_104 = lean_ctor_get(x_51, 0);
lean_inc(x_104);
lean_dec(x_51);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_7);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_43);
x_106 = lean_ctor_get(x_8, 1);
x_107 = lean_ctor_get_uint8(x_106, sizeof(void*)*2 + 3);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_46);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_107);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
if (lean_is_scalar(x_40)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_40;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_52);
return x_112;
}
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_132 = !lean_is_exclusive(x_21);
if (x_132 == 0)
{
return x_21;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_21, 0);
x_134 = lean_ctor_get(x_21, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_21);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_136 = !lean_is_exclusive(x_18);
if (x_136 == 0)
{
return x_18;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_18, 0);
x_138 = lean_ctor_get(x_18, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_18);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_15);
if (x_140 == 0)
{
return x_15;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_15, 0);
x_142 = lean_ctor_get(x_15, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_12);
if (x_144 == 0)
{
return x_12;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_12, 0);
x_146 = lean_ctor_get(x_12, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_12);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 2);
x_18 = lean_ctor_get(x_9, 3);
x_19 = lean_ctor_get(x_9, 4);
x_20 = lean_ctor_get(x_9, 5);
x_21 = lean_ctor_get(x_9, 6);
x_22 = lean_ctor_get(x_9, 7);
x_23 = lean_ctor_get(x_9, 8);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 1);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 2);
x_27 = lean_ctor_get(x_9, 9);
x_28 = l_Lean_Elab_replaceRef(x_11, x_27);
lean_dec(x_27);
lean_dec(x_11);
lean_inc(x_28);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_ctor_set(x_9, 9, x_28);
x_29 = 1;
x_30 = lean_box(0);
lean_inc(x_9);
x_31 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_29, x_30, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_replaceRef(x_12, x_28);
lean_dec(x_28);
lean_dec(x_12);
x_34 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_16);
lean_ctor_set(x_34, 2, x_17);
lean_ctor_set(x_34, 3, x_18);
lean_ctor_set(x_34, 4, x_19);
lean_ctor_set(x_34, 5, x_20);
lean_ctor_set(x_34, 6, x_21);
lean_ctor_set(x_34, 7, x_22);
lean_ctor_set(x_34, 8, x_23);
lean_ctor_set(x_34, 9, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*10 + 1, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*10 + 2, x_26);
x_35 = l_Lean_Elab_Term_ensureHasType(x_13, x_8, x_34, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
lean_inc(x_9);
x_39 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_38, x_30, x_9, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
x_41 = l_Lean_Elab_Term_instantiateMVars(x_7, x_9, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
x_44 = l_Lean_Elab_Term_instantiateMVars(x_36, x_9, x_43);
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
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 11, 8);
lean_closure_set(x_52, 0, x_6);
lean_closure_set(x_52, 1, x_42);
lean_closure_set(x_52, 2, x_46);
lean_closure_set(x_52, 3, x_3);
lean_closure_set(x_52, 4, x_4);
lean_closure_set(x_52, 5, x_51);
lean_closure_set(x_52, 6, x_2);
lean_closure_set(x_52, 7, x_1);
x_53 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_46, x_42, x_50, x_52, x_9, x_47);
lean_dec(x_6);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_42);
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
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 11, 8);
lean_closure_set(x_61, 0, x_6);
lean_closure_set(x_61, 1, x_42);
lean_closure_set(x_61, 2, x_55);
lean_closure_set(x_61, 3, x_3);
lean_closure_set(x_61, 4, x_4);
lean_closure_set(x_61, 5, x_60);
lean_closure_set(x_61, 6, x_2);
lean_closure_set(x_61, 7, x_1);
x_62 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_55, x_42, x_59, x_61, x_9, x_56);
lean_dec(x_6);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
lean_dec(x_42);
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
lean_dec(x_9);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_31);
if (x_73 == 0)
{
return x_31;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_31, 0);
x_75 = lean_ctor_get(x_31, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_31);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_77 = lean_ctor_get(x_9, 0);
x_78 = lean_ctor_get(x_9, 1);
x_79 = lean_ctor_get(x_9, 2);
x_80 = lean_ctor_get(x_9, 3);
x_81 = lean_ctor_get(x_9, 4);
x_82 = lean_ctor_get(x_9, 5);
x_83 = lean_ctor_get(x_9, 6);
x_84 = lean_ctor_get(x_9, 7);
x_85 = lean_ctor_get(x_9, 8);
x_86 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
x_87 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 1);
x_88 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 2);
x_89 = lean_ctor_get(x_9, 9);
lean_inc(x_89);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_9);
x_90 = l_Lean_Elab_replaceRef(x_11, x_89);
lean_dec(x_89);
lean_dec(x_11);
lean_inc(x_90);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_91 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_78);
lean_ctor_set(x_91, 2, x_79);
lean_ctor_set(x_91, 3, x_80);
lean_ctor_set(x_91, 4, x_81);
lean_ctor_set(x_91, 5, x_82);
lean_ctor_set(x_91, 6, x_83);
lean_ctor_set(x_91, 7, x_84);
lean_ctor_set(x_91, 8, x_85);
lean_ctor_set(x_91, 9, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*10, x_86);
lean_ctor_set_uint8(x_91, sizeof(void*)*10 + 1, x_87);
lean_ctor_set_uint8(x_91, sizeof(void*)*10 + 2, x_88);
x_92 = 1;
x_93 = lean_box(0);
lean_inc(x_91);
x_94 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_92, x_93, x_91, x_10);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Elab_replaceRef(x_12, x_90);
lean_dec(x_90);
lean_dec(x_12);
x_97 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_78);
lean_ctor_set(x_97, 2, x_79);
lean_ctor_set(x_97, 3, x_80);
lean_ctor_set(x_97, 4, x_81);
lean_ctor_set(x_97, 5, x_82);
lean_ctor_set(x_97, 6, x_83);
lean_ctor_set(x_97, 7, x_84);
lean_ctor_set(x_97, 8, x_85);
lean_ctor_set(x_97, 9, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*10, x_86);
lean_ctor_set_uint8(x_97, sizeof(void*)*10 + 1, x_87);
lean_ctor_set_uint8(x_97, sizeof(void*)*10 + 2, x_88);
x_98 = l_Lean_Elab_Term_ensureHasType(x_13, x_8, x_97, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = 0;
lean_inc(x_91);
x_102 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_101, x_93, x_91, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_91);
x_104 = l_Lean_Elab_Term_instantiateMVars(x_7, x_91, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_91);
x_107 = l_Lean_Elab_Term_instantiateMVars(x_99, x_91, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_112 = l_Lean_Elab_Command_DefKind_isExample(x_111);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_110);
x_113 = l_Lean_Elab_Command_DefKind_isDefOrAbbrevOrOpaque(x_111);
x_114 = lean_box(x_111);
lean_inc(x_108);
lean_inc(x_105);
lean_inc(x_6);
x_115 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDef___lambda__1___boxed), 11, 8);
lean_closure_set(x_115, 0, x_6);
lean_closure_set(x_115, 1, x_105);
lean_closure_set(x_115, 2, x_108);
lean_closure_set(x_115, 3, x_3);
lean_closure_set(x_115, 4, x_4);
lean_closure_set(x_115, 5, x_114);
lean_closure_set(x_115, 6, x_2);
lean_closure_set(x_115, 7, x_1);
x_116 = l___private_Lean_Elab_Definition_2__withUsedWhen___rarg(x_5, x_6, x_108, x_105, x_113, x_115, x_91, x_109);
lean_dec(x_6);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_91);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_box(0);
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_110;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_99);
lean_dec(x_91);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_102, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_102, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_121 = x_102;
} else {
 lean_dec_ref(x_102);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_91);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_ctor_get(x_98, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_98, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_125 = x_98;
} else {
 lean_dec_ref(x_98);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_94, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_94, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_129 = x_94;
} else {
 lean_dec_ref(x_94);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Elab_Command_mkDef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_13;
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
x_12 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1, x_11, x_3, x_4);
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
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_2);
x_11 = l_Lean_Elab_Command_elabDefVal(x_10, x_2, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Command_mkDef(x_1, x_3, x_4, x_5, x_7, x_6, x_2, x_12, x_8, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 8);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_23 = lean_ctor_get(x_8, 9);
lean_inc(x_23);
x_24 = l_Lean_Elab_replaceRef(x_2, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_14);
lean_ctor_set(x_25, 4, x_15);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_19);
lean_ctor_set(x_25, 9, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*10 + 2, x_22);
x_26 = 0;
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Term_mkFreshTypeMVar(x_26, x_27, x_25, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
lean_inc(x_8);
lean_inc(x_29);
x_32 = l_Lean_Elab_Command_elabDefVal(x_31, x_29, x_8, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Command_mkDef(x_1, x_3, x_4, x_5, x_6, x_7, x_29, x_33, x_8, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
lean_dec(x_10);
lean_inc(x_8);
x_41 = l_Lean_Elab_Term_elabType(x_40, x_8, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 0;
x_45 = lean_box(0);
lean_inc(x_8);
x_46 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_44, x_45, x_8, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_8);
x_48 = l_Lean_Elab_Term_instantiateMVars(x_42, x_8, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_52 = l_Lean_Elab_Command_DefKind_isTheorem(x_51);
lean_inc(x_7);
lean_inc(x_49);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__1), 9, 6);
lean_closure_set(x_53, 0, x_1);
lean_closure_set(x_53, 1, x_49);
lean_closure_set(x_53, 2, x_3);
lean_closure_set(x_53, 3, x_4);
lean_closure_set(x_53, 4, x_5);
lean_closure_set(x_53, 5, x_7);
x_54 = l___private_Lean_Elab_Definition_3__withUsedWhen_x27___rarg(x_6, x_7, x_49, x_52, x_53, x_8, x_50);
lean_dec(x_7);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_41, 0);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_41);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
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
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = l_Lean_Elab_Term_elabBinders___rarg(x_9, x_10, x_6, x_7);
lean_dec(x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = l_Lean_Elab_replaceRef(x_2, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_11);
lean_ctor_set(x_17, 4, x_12);
lean_ctor_set(x_17, 5, x_13);
lean_ctor_set(x_17, 6, x_14);
lean_ctor_set(x_17, 7, x_16);
x_18 = l_Lean_Elab_Command_mkDeclName(x_7, x_4, x_17, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_51 = 2;
x_52 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_19);
x_53 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_19, x_51, x_22, x_52, x_5, x_20);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_5);
x_55 = l_Lean_Elab_Command_getLevelNames(x_5, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_19);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_19);
lean_inc(x_19);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__3), 7, 4);
lean_closure_set(x_59, 0, x_1);
lean_closure_set(x_59, 1, x_19);
lean_closure_set(x_59, 2, x_3);
lean_closure_set(x_59, 3, x_56);
lean_inc(x_5);
x_60 = l___private_Lean_Elab_Command_2__getState(x_5, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l___private_Lean_Elab_Command_8__getVarDecls(x_61);
lean_dec(x_61);
lean_inc(x_5);
x_64 = l___private_Lean_Elab_Command_2__getState(x_5, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l___private_Lean_Elab_Command_6__mkTermContext(x_5, x_65, x_58);
x_68 = l___private_Lean_Elab_Command_7__mkTermState(x_65);
lean_dec(x_65);
x_69 = l_Lean_Elab_Term_elabBinders___rarg(x_63, x_59, x_67, x_68);
lean_dec(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_5);
x_72 = l___private_Lean_Elab_Command_2__getState(x_5, x_66);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 3);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_ctor_get(x_71, 2);
lean_inc(x_78);
lean_dec(x_71);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_74, 5);
lean_dec(x_80);
x_81 = lean_ctor_get(x_74, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_74, 0);
lean_dec(x_82);
lean_ctor_set(x_74, 5, x_77);
lean_ctor_set(x_74, 1, x_78);
lean_ctor_set(x_74, 0, x_76);
lean_inc(x_5);
x_83 = l___private_Lean_Elab_Command_3__setState(x_74, x_5, x_75);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_23 = x_70;
x_24 = x_84;
goto block_50;
}
else
{
uint8_t x_85; 
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_83, 0);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_83);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_74, 2);
x_90 = lean_ctor_get(x_74, 3);
x_91 = lean_ctor_get(x_74, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_74);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_78);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_77);
lean_inc(x_5);
x_93 = l___private_Lean_Elab_Command_3__setState(x_92, x_5, x_75);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_23 = x_70;
x_24 = x_94;
goto block_50;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_99 = !lean_is_exclusive(x_72);
if (x_99 == 0)
{
return x_72;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_72, 0);
x_101 = lean_ctor_get(x_72, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_72);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_69, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
x_104 = lean_ctor_get(x_69, 1);
lean_inc(x_104);
lean_dec(x_69);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_5);
x_106 = l___private_Lean_Elab_Command_2__getState(x_5, x_66);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 3);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_ctor_get(x_104, 2);
lean_inc(x_112);
lean_dec(x_104);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_108, 5);
lean_dec(x_114);
x_115 = lean_ctor_get(x_108, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_108, 0);
lean_dec(x_116);
lean_ctor_set(x_108, 5, x_111);
lean_ctor_set(x_108, 1, x_112);
lean_ctor_set(x_108, 0, x_110);
x_117 = l___private_Lean_Elab_Command_3__setState(x_108, x_5, x_109);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 0, x_105);
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_105);
x_122 = !lean_is_exclusive(x_117);
if (x_122 == 0)
{
return x_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_117, 0);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_117);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_108, 2);
x_127 = lean_ctor_get(x_108, 3);
x_128 = lean_ctor_get(x_108, 4);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_108);
x_129 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_129, 0, x_110);
lean_ctor_set(x_129, 1, x_112);
lean_ctor_set(x_129, 2, x_126);
lean_ctor_set(x_129, 3, x_127);
lean_ctor_set(x_129, 4, x_128);
lean_ctor_set(x_129, 5, x_111);
x_130 = l___private_Lean_Elab_Command_3__setState(x_129, x_5, x_109);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_105);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_105);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_136 = x_130;
} else {
 lean_dec_ref(x_130);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_5);
x_138 = !lean_is_exclusive(x_106);
if (x_138 == 0)
{
return x_106;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_106, 0);
x_140 = lean_ctor_get(x_106, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_106);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_69);
x_142 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_143 = l_unreachable_x21___rarg(x_142);
lean_inc(x_5);
x_144 = lean_apply_2(x_143, x_5, x_66);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_23 = x_145;
x_24 = x_146;
goto block_50;
}
else
{
uint8_t x_147; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_147 = !lean_is_exclusive(x_144);
if (x_147 == 0)
{
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 0);
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_144);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_151 = !lean_is_exclusive(x_64);
if (x_151 == 0)
{
return x_64;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_64, 0);
x_153 = lean_ctor_get(x_64, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_64);
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
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_155 = !lean_is_exclusive(x_60);
if (x_155 == 0)
{
return x_60;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_60, 0);
x_157 = lean_ctor_get(x_60, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_60);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_55);
if (x_159 == 0)
{
return x_55;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_55, 0);
x_161 = lean_ctor_get(x_55, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_55);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_53);
if (x_163 == 0)
{
return x_53;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_53, 0);
x_165 = lean_ctor_get(x_53, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_53);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
block_50:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_5);
x_25 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
lean_inc(x_5);
x_28 = l_Lean_Elab_Command_addDecl(x_27, x_5, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = 0;
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_19);
x_32 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_19, x_30, x_22, x_31, x_5, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_5);
x_34 = l_Lean_Elab_Command_compileDecl(x_27, x_5, x_33);
lean_dec(x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = 1;
x_37 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_19, x_36, x_22, x_31, x_5, x_35);
lean_dec(x_22);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
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
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
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
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_18);
if (x_167 == 0)
{
return x_18;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_18, 0);
x_169 = lean_ctor_get(x_18, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_18);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 7);
x_7 = l_Lean_Elab_replaceRef(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_ctor_set(x_2, 7, x_7);
lean_inc(x_2);
x_8 = l_Lean_Elab_Command_getLevelNames(x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__4___boxed), 6, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_9);
x_13 = l_Lean_Elab_Command_withDeclId___rarg(x_11, x_12, x_2, x_10);
lean_dec(x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
x_24 = lean_ctor_get(x_2, 6);
x_25 = lean_ctor_get(x_2, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_26 = l_Lean_Elab_replaceRef(x_4, x_25);
lean_dec(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_26);
lean_inc(x_27);
x_28 = l_Lean_Elab_Command_getLevelNames(x_27, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDefLike___lambda__4___boxed), 6, 3);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_31);
lean_closure_set(x_32, 2, x_29);
x_33 = l_Lean_Elab_Command_withDeclId___rarg(x_31, x_32, x_27, x_30);
lean_dec(x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_1);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_36 = x_28;
} else {
 lean_dec_ref(x_28);
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
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabDefLike___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabDefLike___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabDefLike___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Definition_4__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_mkDef___lambda__1___closed__2;
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
