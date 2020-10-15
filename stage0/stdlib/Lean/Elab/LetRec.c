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
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwAbort___rarg___closed__1;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___rarg(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_elabBinders___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_28__withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___rarg(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry___main(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__2;
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__1;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___spec__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_match__1(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__8___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2;
extern lean_object* l_Lean_Elab_elabAttr___rarg___lambda__5___closed__2;
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___lambda__5___closed__3;
extern lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__8;
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_18 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_32 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_31, x_2, x_3, x_4, x_5, x_30, x_7, x_8);
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
x_47 = l_Lean_Elab_elabAttr___rarg___lambda__5___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_elabAttr___rarg___lambda__5___closed__3;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
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
x_68 = l_Lean_Elab_elabAttr___rarg___lambda__5___closed__2;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_Elab_elabAttr___rarg___lambda__5___closed__3;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_64);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_1, x_3);
lean_inc(x_9);
lean_inc(x_5);
x_15 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__3(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_push(x_4, x_16);
x_19 = 1;
x_20 = x_3 + x_19;
x_3 = x_20;
x_4 = x_18;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Syntax_getSepArgs(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_empty___closed__1;
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__4(x_9, x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
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
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_23 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
x_29 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
x_40 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__8;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
x_51 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__8___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
x_74 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
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
x_80 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
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
x_91 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__8;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
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
x_102 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__8___closed__2;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__3;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
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
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to infer 'let rec' declaration type");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__3;
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
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("patterns are not allowed in 'let rec' expressions");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_25 = x_14;
x_26 = l_Lean_Syntax_getArg(x_25, x_15);
x_27 = l_Lean_Syntax_isNone(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Syntax_getArg(x_26, x_15);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_3);
x_29 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__1(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = l_Lean_Syntax_getArg(x_25, x_32);
lean_dec(x_25);
x_34 = l_Lean_Syntax_getArg(x_33, x_15);
lean_dec(x_33);
x_35 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_inc(x_34);
x_36 = l_Lean_Syntax_isOfKind(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_37 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_inc(x_34);
x_38 = l_Lean_Syntax_isOfKind(x_34, x_37);
if (x_38 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
lean_inc(x_34);
x_135 = l_Lean_Syntax_isOfKind(x_34, x_134);
x_39 = x_135;
goto block_133;
}
else
{
uint8_t x_136; 
x_136 = 1;
x_39 = x_136;
goto block_133;
}
block_133:
{
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___rarg(x_31);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l_Lean_Syntax_getArg(x_34, x_15);
x_46 = l_Lean_Syntax_getId(x_45);
lean_dec(x_45);
x_47 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_131; 
x_131 = lean_box(0);
x_50 = x_131;
goto block_130;
}
else
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_48, 0);
lean_inc(x_132);
lean_dec(x_48);
x_50 = x_132;
goto block_130;
}
block_130:
{
lean_object* x_51; lean_object* x_52; 
lean_inc(x_46);
x_51 = l_Lean_Name_append___main(x_50, x_46);
lean_dec(x_50);
lean_inc(x_3);
lean_inc(x_51);
x_52 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = 2;
x_55 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_51);
x_56 = l_Lean_Elab_Term_applyAttributesAt(x_51, x_30, x_54, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Syntax_getArg(x_34, x_32);
x_59 = l_Lean_Syntax_getArgs(x_58);
lean_dec(x_58);
x_60 = lean_unsigned_to_nat(2u);
x_61 = l_Lean_Syntax_getArg(x_34, x_60);
x_62 = l_Lean_Elab_Term_expandOptType(x_34, x_61);
lean_dec(x_61);
x_63 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1), 9, 1);
lean_closure_set(x_63, 0, x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_64 = l_Lean_Elab_Term_elabBinders___rarg(x_59, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_59);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
lean_inc(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = 2;
x_71 = lean_box(0);
lean_inc(x_5);
x_72 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_69, x_70, x_71, x_5, x_6, x_7, x_8, x_66);
if (x_38 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(3u);
x_76 = l_Lean_Syntax_getArg(x_34, x_75);
x_77 = lean_st_ref_get(x_8, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_7, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_7, 2);
lean_inc(x_85);
x_86 = lean_st_ref_get(x_8, x_83);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_80);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_90, 0, x_80);
x_91 = x_90;
x_92 = lean_environment_main_module(x_80);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_82);
lean_ctor_set(x_93, 3, x_84);
lean_ctor_set(x_93, 4, x_85);
x_94 = 0;
x_95 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_34, x_76, x_94, x_93, x_89);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_st_ref_take(x_8, x_88);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_99, 1);
lean_dec(x_102);
lean_ctor_set(x_99, 1, x_97);
x_103 = lean_st_ref_set(x_8, x_99, x_100);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_105, 0, x_34);
lean_ctor_set(x_105, 1, x_30);
lean_ctor_set(x_105, 2, x_46);
lean_ctor_set(x_105, 3, x_51);
lean_ctor_set(x_105, 4, x_68);
lean_ctor_set(x_105, 5, x_67);
lean_ctor_set(x_105, 6, x_73);
lean_ctor_set(x_105, 7, x_96);
x_17 = x_105;
x_18 = x_104;
goto block_24;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_99, 0);
x_107 = lean_ctor_get(x_99, 2);
x_108 = lean_ctor_get(x_99, 3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_99);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_97);
lean_ctor_set(x_109, 2, x_107);
lean_ctor_set(x_109, 3, x_108);
x_110 = lean_st_ref_set(x_8, x_109, x_100);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_112, 0, x_34);
lean_ctor_set(x_112, 1, x_30);
lean_ctor_set(x_112, 2, x_46);
lean_ctor_set(x_112, 3, x_51);
lean_ctor_set(x_112, 4, x_68);
lean_ctor_set(x_112, 5, x_67);
lean_ctor_set(x_112, 6, x_73);
lean_ctor_set(x_112, 7, x_96);
x_17 = x_112;
x_18 = x_111;
goto block_24;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_72, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_72, 1);
lean_inc(x_114);
lean_dec(x_72);
x_115 = lean_unsigned_to_nat(4u);
x_116 = l_Lean_Syntax_getArg(x_34, x_115);
x_117 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_117, 0, x_34);
lean_ctor_set(x_117, 1, x_30);
lean_ctor_set(x_117, 2, x_46);
lean_ctor_set(x_117, 3, x_51);
lean_ctor_set(x_117, 4, x_68);
lean_ctor_set(x_117, 5, x_67);
lean_ctor_set(x_117, 6, x_113);
lean_ctor_set(x_117, 7, x_116);
x_17 = x_117;
x_18 = x_114;
goto block_24;
}
}
else
{
uint8_t x_118; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_64);
if (x_118 == 0)
{
return x_64;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_64, 0);
x_120 = lean_ctor_get(x_64, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_64);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_56);
if (x_122 == 0)
{
return x_56;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_56, 0);
x_124 = lean_ctor_get(x_56, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_56);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_52);
if (x_126 == 0)
{
return x_52;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_52, 0);
x_128 = lean_ctor_get(x_52, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_52);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_1);
x_137 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3;
x_138 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_34, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_34);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
return x_138;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_138);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_29);
if (x_143 == 0)
{
return x_29;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_29, 0);
x_145 = lean_ctor_get(x_29, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_29);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_dec(x_26);
x_147 = lean_unsigned_to_nat(1u);
x_148 = l_Lean_Syntax_getArg(x_25, x_147);
lean_dec(x_25);
x_149 = l_Lean_Syntax_getArg(x_148, x_15);
lean_dec(x_148);
x_150 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_inc(x_149);
x_151 = l_Lean_Syntax_isOfKind(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; uint8_t x_154; 
x_152 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_inc(x_149);
x_153 = l_Lean_Syntax_isOfKind(x_149, x_152);
if (x_153 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
lean_inc(x_149);
x_251 = l_Lean_Syntax_isOfKind(x_149, x_250);
x_154 = x_251;
goto block_249;
}
else
{
uint8_t x_252; 
x_252 = 1;
x_154 = x_252;
goto block_249;
}
block_249:
{
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_149);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_155 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___rarg(x_9);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
return x_155;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_155);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = l_Lean_Syntax_getArg(x_149, x_15);
x_161 = l_Lean_Syntax_getId(x_160);
lean_dec(x_160);
x_162 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_165 = x_247;
goto block_246;
}
else
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_163, 0);
lean_inc(x_248);
lean_dec(x_163);
x_165 = x_248;
goto block_246;
}
block_246:
{
lean_object* x_166; lean_object* x_167; 
lean_inc(x_161);
x_166 = l_Lean_Name_append___main(x_165, x_161);
lean_dec(x_165);
lean_inc(x_3);
lean_inc(x_166);
x_167 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6(x_166, x_3, x_4, x_5, x_6, x_7, x_8, x_164);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = l_Array_empty___closed__1;
x_170 = 2;
x_171 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_166);
x_172 = l_Lean_Elab_Term_applyAttributesAt(x_166, x_169, x_170, x_171, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Lean_Syntax_getArg(x_149, x_147);
x_175 = l_Lean_Syntax_getArgs(x_174);
lean_dec(x_174);
x_176 = lean_unsigned_to_nat(2u);
x_177 = l_Lean_Syntax_getArg(x_149, x_176);
x_178 = l_Lean_Elab_Term_expandOptType(x_149, x_177);
lean_dec(x_177);
x_179 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1), 9, 1);
lean_closure_set(x_179, 0, x_178);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_180 = l_Lean_Elab_Term_elabBinders___rarg(x_175, x_179, x_3, x_4, x_5, x_6, x_7, x_8, x_173);
lean_dec(x_175);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
lean_inc(x_183);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_183);
x_186 = 2;
x_187 = lean_box(0);
lean_inc(x_5);
x_188 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_185, x_186, x_187, x_5, x_6, x_7, x_8, x_182);
if (x_153 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_unsigned_to_nat(3u);
x_192 = l_Lean_Syntax_getArg(x_149, x_191);
x_193 = lean_st_ref_get(x_8, x_190);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
lean_dec(x_194);
x_197 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_195);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_7, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_7, 2);
lean_inc(x_201);
x_202 = lean_st_ref_get(x_8, x_199);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_196);
x_206 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_206, 0, x_196);
x_207 = x_206;
x_208 = lean_environment_main_module(x_196);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_198);
lean_ctor_set(x_209, 3, x_200);
lean_ctor_set(x_209, 4, x_201);
x_210 = 0;
x_211 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_149, x_192, x_210, x_209, x_205);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_st_ref_take(x_8, x_204);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = !lean_is_exclusive(x_215);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_215, 1);
lean_dec(x_218);
lean_ctor_set(x_215, 1, x_213);
x_219 = lean_st_ref_set(x_8, x_215, x_216);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_221, 0, x_149);
lean_ctor_set(x_221, 1, x_169);
lean_ctor_set(x_221, 2, x_161);
lean_ctor_set(x_221, 3, x_166);
lean_ctor_set(x_221, 4, x_184);
lean_ctor_set(x_221, 5, x_183);
lean_ctor_set(x_221, 6, x_189);
lean_ctor_set(x_221, 7, x_212);
x_17 = x_221;
x_18 = x_220;
goto block_24;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_215, 0);
x_223 = lean_ctor_get(x_215, 2);
x_224 = lean_ctor_get(x_215, 3);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_215);
x_225 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_213);
lean_ctor_set(x_225, 2, x_223);
lean_ctor_set(x_225, 3, x_224);
x_226 = lean_st_ref_set(x_8, x_225, x_216);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_228, 0, x_149);
lean_ctor_set(x_228, 1, x_169);
lean_ctor_set(x_228, 2, x_161);
lean_ctor_set(x_228, 3, x_166);
lean_ctor_set(x_228, 4, x_184);
lean_ctor_set(x_228, 5, x_183);
lean_ctor_set(x_228, 6, x_189);
lean_ctor_set(x_228, 7, x_212);
x_17 = x_228;
x_18 = x_227;
goto block_24;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_188, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_188, 1);
lean_inc(x_230);
lean_dec(x_188);
x_231 = lean_unsigned_to_nat(4u);
x_232 = l_Lean_Syntax_getArg(x_149, x_231);
x_233 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_233, 0, x_149);
lean_ctor_set(x_233, 1, x_169);
lean_ctor_set(x_233, 2, x_161);
lean_ctor_set(x_233, 3, x_166);
lean_ctor_set(x_233, 4, x_184);
lean_ctor_set(x_233, 5, x_183);
lean_ctor_set(x_233, 6, x_229);
lean_ctor_set(x_233, 7, x_232);
x_17 = x_233;
x_18 = x_230;
goto block_24;
}
}
else
{
uint8_t x_234; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec(x_149);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_180);
if (x_234 == 0)
{
return x_180;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_180, 0);
x_236 = lean_ctor_get(x_180, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_180);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec(x_149);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_172);
if (x_238 == 0)
{
return x_172;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_172, 0);
x_240 = lean_ctor_get(x_172, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_172);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec(x_149);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_167);
if (x_242 == 0)
{
return x_167;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_167, 0);
x_244 = lean_ctor_get(x_167, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_167);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_16);
lean_dec(x_1);
x_253 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3;
x_254 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_149, x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_149);
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
return x_254;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_254);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
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
}
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getSepArgs(x_10);
lean_dec(x_10);
x_12 = x_11;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7), 9, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = x_14;
x_16 = lean_apply_7(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
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
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_28__withLetDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___spec__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = lean_array_push(x_2, x_5);
x_16 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg(x_3, x_4, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
x_20 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___spec__1___rarg(x_16, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1___boxed), 9, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_withDeclName___rarg(x_11, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___spec__1___lambda__1), 10, 1);
lean_closure_set(x_21, 0, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(x_18, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = x_9;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___spec__1), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = x_12;
x_14 = lean_apply_7(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbort___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_15 = l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___rarg(x_12);
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
x_21 = l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___rarg(x_17);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbort___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_abortIfContainsSyntheticSorry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___spec__1(x_2, x_3, x_11, x_13, x_16, x_15);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_12 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_21 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(x_3, x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1(x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
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
x_10 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_15 = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___rarg(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letrec");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetRec___closed__3() {
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
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___lambda__1___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___spec__7___closed__3);
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
