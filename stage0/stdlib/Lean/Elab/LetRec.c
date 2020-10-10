// Lean compiler output
// Module: Lean.Elab.LetRec
// Imports: Init Lean.Elab.Attributes Lean.Elab.Binders Lean.Elab.DeclModifiers Lean.Elab.SyntheticMVars
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
lean_object* l_Lean_Elab_Term_elabLetRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_1__mkLetRecDeclView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l___private_Lean_Elab_LetRec_5__abortIfContainsSyntheticSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_6__registerLetRecsToLift___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_4__elabLetRecDeclValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_4__elabLetRecDeclValues___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_6__registerLetRecsToLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_object* l_Lean_Elab_Term_elabLetRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_5__abortIfContainsSyntheticSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_3__withAuxLocalDecls(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__1;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_elabBinders___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_expandDeclId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_4__elabLetRecDeclValues___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_6__registerLetRecsToLift___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry___main(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__3;
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_1__mkLetRecDeclView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec(lean_object*);
lean_object* l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3;
lean_object* l___private_Lean_Elab_LetRec_6__registerLetRecsToLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__2;
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__4;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__3;
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_LetRec_3__withAuxLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux(lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__2;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
x_14 = l_Lean_Environment_contains(x_13, x_1);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
lean_inc(x_13);
x_15 = l_Lean_mkPrivateName(x_13, x_1);
lean_inc(x_13);
x_16 = l_Lean_Environment_contains(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_2);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Environment_contains(x_13, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_9);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_13);
lean_free_object(x_9);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_1);
x_29 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_13);
lean_free_object(x_9);
lean_inc(x_1);
x_38 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_1);
x_40 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_1);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
lean_dec(x_38);
x_50 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_62);
x_63 = l_Lean_Environment_contains(x_62, x_1);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_inc(x_1);
lean_inc(x_62);
x_64 = l_Lean_mkPrivateName(x_62, x_1);
lean_inc(x_62);
x_65 = l_Lean_Environment_contains(x_62, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_Environment_contains(x_62, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_2);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_61);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_69);
x_74 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_62);
x_79 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_79, 0, x_1);
x_80 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__3;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; 
lean_dec(x_62);
lean_inc(x_1);
x_89 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_90, 0, x_1);
x_91 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
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
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_100 = lean_ctor_get(x_89, 0);
lean_inc(x_100);
lean_dec(x_89);
x_101 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__3;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isIdOrAtom_x3f(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_6, 3);
x_14 = l_Lean_replaceRef(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_replaceRef(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_ctor_set(x_6, 3, x_16);
x_17 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_18 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 2);
x_26 = lean_ctor_get(x_6, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_27 = l_Lean_replaceRef(x_10, x_26);
lean_dec(x_10);
x_28 = l_Lean_replaceRef(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_replaceRef(x_28, x_26);
lean_dec(x_26);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_32 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_31, x_2, x_3, x_4, x_5, x_30, x_7, x_8);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_box(0);
x_39 = lean_name_mk_string(x_38, x_37);
x_40 = lean_st_ref_get(x_7, x_8);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_isAttribute(x_44, x_39);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_40);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_39);
x_47 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_6);
lean_dec(x_2);
x_56 = lean_unsigned_to_nat(1u);
x_57 = l_Lean_Syntax_getArg(x_1, x_56);
x_58 = l_Lean_Syntax_getNumArgs(x_57);
x_59 = lean_nat_dec_eq(x_58, x_9);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_39);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_40, 0, x_60);
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_57);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_40, 0, x_62);
return x_40;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_40, 0);
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_40);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_isAttribute(x_65, x_39);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_67, 0, x_39);
x_68 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_64);
lean_dec(x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_2);
x_77 = lean_unsigned_to_nat(1u);
x_78 = l_Lean_Syntax_getArg(x_1, x_77);
x_79 = l_Lean_Syntax_getNumArgs(x_78);
x_80 = lean_nat_dec_eq(x_79, x_9);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_39);
lean_ctor_set(x_81, 1, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_64);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_39);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_64);
return x_85;
}
}
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_5);
x_16 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__5(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_4, x_17);
x_20 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_19;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Syntax_getArgs(x_1);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__6(x_10, x_9, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__4(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_11;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to infer 'let rec' declaration type");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_elabType(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__3;
x_14 = l_Lean_Elab_Term_registerCustomErrorIfMVar(x_11, x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
x_16 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_array_get_size(x_2);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_array_get_size(x_2);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("patterns are not allowed in 'let rec' expressions");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_140; uint8_t x_141; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_25 = x_14;
x_140 = l_Lean_Syntax_getArg(x_25, x_15);
x_141 = l_Lean_Syntax_isNone(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Syntax_getArg(x_140, x_15);
lean_dec(x_140);
lean_inc(x_7);
lean_inc(x_3);
x_143 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__3(x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_26 = x_144;
x_27 = x_145;
goto block_139;
}
else
{
uint8_t x_146; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_143);
if (x_146 == 0)
{
return x_143;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_143, 0);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_143);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; 
lean_dec(x_140);
x_150 = l_Array_empty___closed__1;
x_26 = x_150;
x_27 = x_9;
goto block_139;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = x_17;
x_22 = lean_array_fset(x_16, x_1, x_21);
lean_dec(x_1);
x_1 = x_20;
x_2 = x_22;
x_9 = x_18;
goto _start;
}
block_139:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_Syntax_getArg(x_25, x_28);
lean_dec(x_25);
x_30 = l_Lean_Syntax_getArg(x_29, x_15);
lean_dec(x_29);
x_31 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_inc(x_30);
x_34 = l_Lean_Syntax_isOfKind(x_30, x_33);
if (x_34 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
lean_inc(x_30);
x_125 = l_Lean_Syntax_isOfKind(x_30, x_124);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2___rarg(x_27);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_126);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
x_131 = lean_box(0);
x_35 = x_131;
goto block_123;
}
}
else
{
lean_object* x_132; 
x_132 = lean_box(0);
x_35 = x_132;
goto block_123;
}
block_123:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
x_36 = l_Lean_Syntax_getIdAt(x_30, x_15);
x_37 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_27);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_121; 
x_121 = lean_box(0);
x_40 = x_121;
goto block_120;
}
else
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_38, 0);
lean_inc(x_122);
lean_dec(x_38);
x_40 = x_122;
goto block_120;
}
block_120:
{
lean_object* x_41; lean_object* x_42; 
lean_inc(x_36);
x_41 = l_Lean_Name_append___main(x_40, x_36);
lean_dec(x_40);
lean_inc(x_3);
lean_inc(x_41);
x_42 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = 2;
x_45 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_41);
x_46 = l_Lean_Elab_Term_applyAttributesAt(x_41, x_26, x_44, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Syntax_getArg(x_30, x_28);
x_49 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_getArg(x_30, x_50);
x_52 = l_Lean_Elab_Term_expandOptType(x_30, x_51);
lean_dec(x_51);
x_53 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1), 9, 1);
lean_closure_set(x_53, 0, x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lean_Elab_Term_elabBinders___rarg(x_49, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = 2;
x_61 = lean_box(0);
lean_inc(x_5);
x_62 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_59, x_60, x_61, x_5, x_6, x_7, x_8, x_56);
if (x_34 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(3u);
x_66 = l_Lean_Syntax_getArg(x_30, x_65);
x_67 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_8, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_st_ref_get(x_8, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_7, 2);
lean_inc(x_79);
lean_inc(x_73);
x_80 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_80, 0, x_73);
x_81 = x_80;
x_82 = lean_environment_main_module(x_73);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_68);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_79);
x_84 = 0;
x_85 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_30, x_66, x_84, x_83, x_77);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_take(x_8, x_76);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_89, 1);
lean_dec(x_92);
lean_ctor_set(x_89, 1, x_87);
x_93 = lean_st_ref_set(x_8, x_89, x_90);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_95, 0, x_30);
lean_ctor_set(x_95, 1, x_26);
lean_ctor_set(x_95, 2, x_36);
lean_ctor_set(x_95, 3, x_41);
lean_ctor_set(x_95, 4, x_58);
lean_ctor_set(x_95, 5, x_57);
lean_ctor_set(x_95, 6, x_63);
lean_ctor_set(x_95, 7, x_86);
x_17 = x_95;
x_18 = x_94;
goto block_24;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_89, 0);
x_97 = lean_ctor_get(x_89, 2);
x_98 = lean_ctor_get(x_89, 3);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_89);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_87);
lean_ctor_set(x_99, 2, x_97);
lean_ctor_set(x_99, 3, x_98);
x_100 = lean_st_ref_set(x_8, x_99, x_90);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_102, 0, x_30);
lean_ctor_set(x_102, 1, x_26);
lean_ctor_set(x_102, 2, x_36);
lean_ctor_set(x_102, 3, x_41);
lean_ctor_set(x_102, 4, x_58);
lean_ctor_set(x_102, 5, x_57);
lean_ctor_set(x_102, 6, x_63);
lean_ctor_set(x_102, 7, x_86);
x_17 = x_102;
x_18 = x_101;
goto block_24;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_62, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_62, 1);
lean_inc(x_104);
lean_dec(x_62);
x_105 = lean_unsigned_to_nat(4u);
x_106 = l_Lean_Syntax_getArg(x_30, x_105);
x_107 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_107, 0, x_30);
lean_ctor_set(x_107, 1, x_26);
lean_ctor_set(x_107, 2, x_36);
lean_ctor_set(x_107, 3, x_41);
lean_ctor_set(x_107, 4, x_58);
lean_ctor_set(x_107, 5, x_57);
lean_ctor_set(x_107, 6, x_103);
lean_ctor_set(x_107, 7, x_106);
x_17 = x_107;
x_18 = x_104;
goto block_24;
}
}
else
{
uint8_t x_108; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_54);
if (x_108 == 0)
{
return x_54;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_54, 0);
x_110 = lean_ctor_get(x_54, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_54);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_46);
if (x_112 == 0)
{
return x_46;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_46, 0);
x_114 = lean_ctor_get(x_46, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_46);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_42);
if (x_116 == 0)
{
return x_42;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_42, 0);
x_118 = lean_ctor_get(x_42, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_42);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_1);
x_133 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__3;
x_134 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_30, x_133, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_LetRec_1__mkLetRecDeclView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_empty___closed__1;
x_15 = l_Array_foldlStepMAux___main___at_Lean_Elab_expandDeclId___spec__1(x_12, x_11, x_13, x_14);
lean_dec(x_11);
x_16 = x_15;
x_17 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7), 9, 2);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_16);
x_18 = x_17;
x_19 = lean_apply_7(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_LetRec_1__mkLetRecDeclView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_LetRec_1__mkLetRecDeclView(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = lean_array_push(x_2, x_5);
x_16 = l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg(x_3, x_4, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_fget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 6);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
x_20 = l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_16, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_LetRec_3__withAuxLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_LetRec_2__withAuxLocalDeclsAux___main___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_LetRec_3__withAuxLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_3__withAuxLocalDecls___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_4__elabLetRecDeclValues___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 7);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 11, 4);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1___boxed), 9, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_withDeclName___rarg(x_11, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_4__elabLetRecDeclValues___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = lean_ctor_get(x_17, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 4);
lean_inc(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_4__elabLetRecDeclValues___spec__1___lambda__1), 10, 1);
lean_closure_set(x_21, 0, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_18, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
x_27 = x_23;
x_28 = lean_array_fset(x_16, x_1, x_27);
lean_dec(x_1);
x_1 = x_26;
x_2 = x_28;
x_9 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_Lean_Elab_LetRec_4__elabLetRecDeclValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = x_9;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_4__elabLetRecDeclValues___spec__1), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = x_12;
x_14 = lean_apply_7(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l___private_Lean_Elab_LetRec_5__abortIfContainsSyntheticSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_hasSyntheticSorry___main(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; 
lean_free_object(x_9);
x_15 = l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = l_Lean_Expr_hasSyntheticSorry___main(x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(x_17);
return x_21;
}
}
}
}
lean_object* l___private_Lean_Elab_LetRec_5__abortIfContainsSyntheticSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_LetRec_5__abortIfContainsSyntheticSorry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_6__registerLetRecsToLift___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = x_6;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = lean_array_fget(x_6, x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_6, x_5, x_11);
x_13 = x_10;
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 6);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_1, x_5);
x_22 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec(x_21);
x_23 = lean_array_get(x_20, x_2, x_5);
x_24 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_3);
lean_ctor_set(x_25, 6, x_4);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_23);
lean_ctor_set(x_25, 9, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
x_28 = x_25;
x_29 = lean_array_fset(x_12, x_5, x_28);
lean_dec(x_5);
x_5 = x_27;
x_6 = x_29;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_LetRec_6__registerLetRecsToLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_elabBinders___spec__1___rarg(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = x_1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_6__registerLetRecsToLift___spec__1(x_2, x_3, x_11, x_13, x_16, x_15);
x_18 = x_17;
x_19 = lean_st_ref_take(x_5, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 3);
x_24 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_25 = l_List_append___rarg(x_24, x_23);
lean_ctor_set(x_20, 3, x_25);
x_26 = lean_st_ref_set(x_5, x_20, x_21);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
x_35 = lean_ctor_get(x_20, 2);
x_36 = lean_ctor_get(x_20, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_37 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_38 = l_List_append___rarg(x_37, x_36);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_st_ref_set(x_5, x_39, x_21);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_6__registerLetRecsToLift___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_6__registerLetRecsToLift___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_LetRec_6__registerLetRecsToLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_LetRec_6__registerLetRecsToLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabLetRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_LetRec_4__elabLetRecDeclValues(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Elab_Term_elabTermEnsuringType(x_15, x_2, x_17, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
x_21 = l___private_Lean_Elab_LetRec_6__registerLetRecsToLift(x_3, x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1(x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_LetRec_1__mkLetRecDeclView(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___lambda__1), 11, 3);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
x_15 = l___private_Lean_Elab_LetRec_3__withAuxLocalDecls___rarg(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabLetRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letrec");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Attributes(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_LetRec(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___lambda__1___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_1__mkLetRecDeclView___spec__7___closed__3);
l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabLetRec(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
