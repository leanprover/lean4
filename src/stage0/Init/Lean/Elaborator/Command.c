// Lean compiler output
// Module: Init.Lean.Elaborator.Command
// Imports: Init.Lean.Elaborator.Alias Init.Lean.Elaborator.Basic Init.Lean.Elaborator.ResolveName Init.Lean.Elaborator.Term
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
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
lean_object* l_Lean_Elab_elabNotation___rarg(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection(lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addOpenDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenSimple(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
lean_object* l_Lean_Elab_elabInitQuot___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Array_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runIOUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabEnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpen(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
lean_object* l_Lean_Elab_elabEnd___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix(lean_object*);
lean_object* l_Lean_Elab_elabExport___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
lean_object* l_Lean_Elab_addUniverse___closed__2;
extern lean_object* l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSection___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenHiding(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Elab_elabResolveName(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode___rarg(lean_object*);
lean_object* l_Lean_Elab_elabInitQuot(lean_object*);
lean_object* l_Lean_Elab_elabElab(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse(lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
extern lean_object* l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_addUniverse___closed__1;
lean_object* l_Lean_Elab_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabVariable(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabMixfix___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses(lean_object*);
lean_object* l_Lean_Elab_elabUniverses(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes___boxed(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
lean_object* l_Lean_Elab_elabNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabMixfix___rarg(lean_object*);
lean_object* l_Lean_Syntax_lift(lean_object*, lean_object*);
lean_object* l_Lean_Elab_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope___boxed(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Elab_getNamespace___rarg(lean_object*);
lean_object* l_Lean_Elab_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve(lean_object*);
lean_object* l_Lean_Elab_elabElab___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabExport___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Elab_addUniverse___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabElab___closed__2;
lean_object* l_Lean_Elab_elabExport___closed__2;
lean_object* l_Lean_Syntax_getArgs___rarg(lean_object*);
lean_object* l_IO_println___at_Lean_Elab_elabElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__2;
lean_object* l_Lean_Syntax_getId___rarg(lean_object*);
lean_object* l_Lean_Elab_elabExport(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__2;
lean_object* l_Lean_Elab_getUniverses___rarg(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_elabNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___at_Lean_Elab_elabElab___spec__2(lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_getScope___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabNotation___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
lean_object* l_Lean_Elab_elabEnd___closed__6;
uint8_t l_Lean_Name_eqStr(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(lean_object*);
lean_object* l_Lean_Elab_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabPreTerm___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* l_Lean_Elab_elabTermAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
lean_object* l_Lean_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabReserve___rarg(lean_object*);
uint8_t l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
lean_object* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabEnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__5;
lean_object* l_Lean_Elab_getEnv___rarg(lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabElab___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
lean_object* l_Lean_Elab_getPosition(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__3;
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabResolveName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenOnly(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
lean_object* l_Lean_Elab_elabEnd___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_reserve___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
lean_object* l_Lean_Elab_logElabException(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot___boxed(lean_object*);
lean_object* l_Lean_Elab_elabMixfix(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabNotation(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(lean_object*);
lean_object* l_Lean_Elab_elabReserve(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
extern lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
lean_object* l_Lean_Elab_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Elab_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabReserve___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_1, x_2, x_5, x_4);
x_8 = l_List_head_x21___at_Lean_Elab_getScope___spec__1(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_8, 3);
x_11 = lean_ctor_get(x_8, 7);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 6);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 5);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_inc(x_6);
x_19 = lean_name_mk_string(x_18, x_6);
x_20 = lean_box(0);
if (x_2 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_6);
x_21 = l_Lean_Options_empty;
x_22 = l_Lean_LocalContext_Inhabited___closed__1;
x_23 = lean_unsigned_to_nat(1u);
x_24 = 0;
lean_ctor_set(x_8, 7, x_23);
lean_ctor_set(x_8, 6, x_22);
lean_ctor_set(x_8, 5, x_20);
lean_ctor_set(x_8, 4, x_20);
lean_ctor_set(x_8, 2, x_21);
lean_ctor_set(x_8, 1, x_19);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_24);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_name_mk_string(x_10, x_6);
x_27 = l_Lean_Options_empty;
x_28 = l_Lean_LocalContext_Inhabited___closed__1;
x_29 = lean_unsigned_to_nat(1u);
x_30 = 0;
lean_ctor_set(x_8, 7, x_29);
lean_ctor_set(x_8, 6, x_28);
lean_ctor_set(x_8, 5, x_20);
lean_ctor_set(x_8, 4, x_20);
lean_ctor_set(x_8, 3, x_26);
lean_ctor_set(x_8, 2, x_27);
lean_ctor_set(x_8, 1, x_19);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_8, 3);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_box(0);
lean_inc(x_6);
x_34 = lean_name_mk_string(x_33, x_6);
x_35 = lean_box(0);
if (x_2 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
x_36 = l_Lean_Options_empty;
x_37 = l_Lean_LocalContext_Inhabited___closed__1;
x_38 = lean_unsigned_to_nat(1u);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_35);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_name_mk_string(x_32, x_6);
x_43 = l_Lean_Options_empty;
x_44 = l_Lean_LocalContext_Inhabited___closed__1;
x_45 = lean_unsigned_to_nat(1u);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_35);
lean_ctor_set(x_47, 5, x_35);
lean_ctor_set(x_47, 6, x_44);
lean_ctor_set(x_47, 7, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*8, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
default: 
{
lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_box(0);
return x_49;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_Elaborator_Command_1__addScopes(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_array_get(x_8, x_5, x_9);
x_11 = l_Lean_Syntax_getId___rarg(x_10);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_6, 5);
x_14 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_15 = 1;
x_16 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_14, x_15, x_11, x_13);
lean_dec(x_13);
lean_ctor_set(x_6, 5, x_16);
x_17 = lean_box(0);
lean_ctor_set(x_3, 0, x_17);
x_18 = l_Lean_Elab_getNamespace___rarg(x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_20, 0);
x_24 = l_Lean_registerNamespace(x_23, x_22);
lean_ctor_set(x_20, 0, x_24);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 2);
x_29 = lean_ctor_get(x_20, 3);
x_30 = lean_ctor_get(x_20, 4);
x_31 = lean_ctor_get(x_20, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_32 = l_Lean_registerNamespace(x_26, x_25);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_31);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 5);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
x_43 = l_Lean_registerNamespace(x_36, x_35);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
x_48 = lean_ctor_get(x_6, 2);
x_49 = lean_ctor_get(x_6, 3);
x_50 = lean_ctor_get(x_6, 4);
x_51 = lean_ctor_get(x_6, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_52 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_53 = 1;
x_54 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_52, x_53, x_11, x_51);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_49);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set(x_55, 5, x_54);
x_56 = lean_box(0);
lean_ctor_set(x_3, 1, x_55);
lean_ctor_set(x_3, 0, x_56);
x_57 = l_Lean_Elab_getNamespace___rarg(x_3);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 5);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
 x_67 = lean_box(0);
}
x_68 = l_Lean_registerNamespace(x_61, x_59);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_63);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set(x_69, 4, x_65);
lean_ctor_set(x_69, 5, x_66);
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_71 = lean_ctor_get(x_1, 1);
x_72 = lean_ctor_get(x_3, 1);
lean_inc(x_72);
lean_dec(x_3);
x_73 = lean_box(0);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_array_get(x_73, x_71, x_74);
x_76 = l_Lean_Syntax_getId___rarg(x_75);
lean_dec(x_75);
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_72, 5);
lean_inc(x_82);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_83 = x_72;
} else {
 lean_dec_ref(x_72);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_85 = 1;
x_86 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_84, x_85, x_76, x_82);
lean_dec(x_82);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(0, 6, 0);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set(x_87, 3, x_80);
lean_ctor_set(x_87, 4, x_81);
lean_ctor_set(x_87, 5, x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_Elab_getNamespace___rarg(x_89);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_91, 5);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
x_101 = l_Lean_registerNamespace(x_94, x_92);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 6, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
lean_ctor_set(x_102, 2, x_96);
lean_ctor_set(x_102, 3, x_97);
lean_ctor_set(x_102, 4, x_98);
lean_ctor_set(x_102, 5, x_99);
if (lean_is_scalar(x_93)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_93;
}
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
lean_object* l_Lean_Elab_elabNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabNamespace(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNamespace");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabNamespace___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_getNamespace___rarg(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = l_Lean_Syntax_getOptionalIdent___rarg(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_8, 5);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_17 = lean_box(0);
x_18 = l_Lean_Options_empty;
x_19 = l_Lean_LocalContext_Inhabited___closed__1;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_7);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_15);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*8, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_8, 5, x_22);
x_23 = lean_box(0);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_30 = lean_box(0);
x_31 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_32 = lean_box(0);
x_33 = l_Lean_Options_empty;
x_34 = l_Lean_LocalContext_Inhabited___closed__1;
x_35 = 0;
x_36 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_7);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_10);
lean_ctor_set_uint8(x_36, sizeof(void*)*8, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
lean_ctor_set(x_38, 3, x_27);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_37);
x_39 = lean_box(0);
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_7);
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_8, 5);
x_43 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_44 = 0;
x_45 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_43, x_44, x_40, x_42);
lean_dec(x_42);
lean_ctor_set(x_8, 5, x_45);
x_46 = lean_box(0);
lean_ctor_set(x_5, 0, x_46);
return x_5;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
x_49 = lean_ctor_get(x_8, 2);
x_50 = lean_ctor_get(x_8, 3);
x_51 = lean_ctor_get(x_8, 4);
x_52 = lean_ctor_get(x_8, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
x_53 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_54 = 0;
x_55 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_53, x_54, x_40, x_52);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_51);
lean_ctor_set(x_56, 5, x_55);
x_57 = lean_box(0);
lean_ctor_set(x_5, 1, x_56);
lean_ctor_set(x_5, 0, x_57);
return x_5;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_5);
x_60 = lean_box(0);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_array_get(x_60, x_4, x_61);
x_63 = l_Lean_Syntax_getOptionalIdent___rarg(x_62);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_59, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
x_72 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_73 = lean_box(0);
x_74 = l_Lean_Options_empty;
x_75 = l_Lean_LocalContext_Inhabited___closed__1;
x_76 = 0;
x_77 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_58);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_71);
lean_ctor_set(x_77, 6, x_75);
lean_ctor_set(x_77, 7, x_61);
lean_ctor_set_uint8(x_77, sizeof(void*)*8, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_69);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 6, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_65);
lean_ctor_set(x_79, 2, x_66);
lean_ctor_set(x_79, 3, x_67);
lean_ctor_set(x_79, 4, x_68);
lean_ctor_set(x_79, 5, x_78);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_58);
x_82 = lean_ctor_get(x_63, 0);
lean_inc(x_82);
lean_dec(x_63);
x_83 = lean_ctor_get(x_59, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_59, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_59, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_59, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_59, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_59, 5);
lean_inc(x_88);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_89 = x_59;
} else {
 lean_dec_ref(x_59);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_91 = 0;
x_92 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_90, x_91, x_82, x_88);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 6, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_84);
lean_ctor_set(x_93, 2, x_85);
lean_ctor_set(x_93, 3, x_86);
lean_ctor_set(x_93, 4, x_87);
lean_ctor_set(x_93, 5, x_92);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
lean_object* l_Lean_Elab_elabSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabSection(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSection");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabSection___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_getNumParts___main(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_box(0);
x_6 = lean_name_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_Name_eqStr(x_9, x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
default: 
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_8, x_10);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_get(x_12, x_9, x_13);
x_15 = l_Lean_Syntax_getOptionalIdent___rarg(x_14);
lean_dec(x_14);
x_16 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_15);
x_17 = lean_nat_dec_lt(x_16, x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_19 = l_List_drop___main___rarg(x_18, x_8);
lean_dec(x_8);
lean_ctor_set(x_5, 5, x_19);
x_20 = l_Lean_Elab_elabEnd___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
x_21 = l_List_drop___main___rarg(x_16, x_8);
lean_ctor_set(x_5, 5, x_21);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_22; 
x_22 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_8);
lean_dec(x_8);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Elab_elabEnd___closed__4;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
lean_ctor_set(x_3, 0, x_24);
return x_3;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_25, x_8);
lean_dec(x_8);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Elab_elabEnd___closed__6;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; 
x_28 = lean_box(0);
lean_ctor_set(x_3, 0, x_28);
return x_3;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_List_lengthAux___main___rarg(x_34, x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_array_get(x_38, x_35, x_39);
x_41 = l_Lean_Syntax_getOptionalIdent___rarg(x_40);
lean_dec(x_40);
x_42 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_41);
x_43 = lean_nat_dec_lt(x_42, x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_41);
x_44 = lean_nat_sub(x_37, x_39);
lean_dec(x_37);
x_45 = l_List_drop___main___rarg(x_44, x_34);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_32);
lean_ctor_set(x_46, 4, x_33);
lean_ctor_set(x_46, 5, x_45);
x_47 = l_Lean_Elab_elabEnd___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_46);
lean_ctor_set(x_3, 0, x_47);
return x_3;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
x_48 = l_List_drop___main___rarg(x_42, x_34);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_30);
lean_ctor_set(x_49, 2, x_31);
lean_ctor_set(x_49, 3, x_32);
lean_ctor_set(x_49, 4, x_33);
lean_ctor_set(x_49, 5, x_48);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_50; 
x_50 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_34);
lean_dec(x_34);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lean_Elab_elabEnd___closed__4;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_52);
return x_3;
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
x_54 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_53, x_34);
lean_dec(x_34);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Elab_elabEnd___closed__6;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_55);
return x_3;
}
else
{
lean_object* x_56; 
x_56 = lean_box(0);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_56);
return x_3;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_1, 1);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_List_lengthAux___main___rarg(x_63, x_66);
x_68 = lean_box(0);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_array_get(x_68, x_65, x_69);
x_71 = l_Lean_Syntax_getOptionalIdent___rarg(x_70);
lean_dec(x_70);
x_72 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_71);
x_73 = lean_nat_dec_lt(x_72, x_67);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_72);
lean_dec(x_71);
x_74 = lean_nat_sub(x_67, x_69);
lean_dec(x_67);
x_75 = l_List_drop___main___rarg(x_74, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_64)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_64;
}
lean_ctor_set(x_76, 0, x_58);
lean_ctor_set(x_76, 1, x_59);
lean_ctor_set(x_76, 2, x_60);
lean_ctor_set(x_76, 3, x_61);
lean_ctor_set(x_76, 4, x_62);
lean_ctor_set(x_76, 5, x_75);
x_77 = l_Lean_Elab_elabEnd___closed__2;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
x_79 = l_List_drop___main___rarg(x_72, x_63);
if (lean_is_scalar(x_64)) {
 x_80 = lean_alloc_ctor(0, 6, 0);
} else {
 x_80 = x_64;
}
lean_ctor_set(x_80, 0, x_58);
lean_ctor_set(x_80, 1, x_59);
lean_ctor_set(x_80, 2, x_60);
lean_ctor_set(x_80, 3, x_61);
lean_ctor_set(x_80, 4, x_62);
lean_ctor_set(x_80, 5, x_79);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_81; 
x_81 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_63);
lean_dec(x_63);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lean_Elab_elabEnd___closed__4;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_71, 0);
lean_inc(x_86);
lean_dec(x_71);
x_87 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_86, x_63);
lean_dec(x_63);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Elab_elabEnd___closed__6;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
return x_91;
}
}
}
}
}
}
lean_object* l_Lean_Elab_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabEnd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabEnd");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabEnd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_array_fget(x_5, x_6);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_19 = l_Lean_Syntax_getId___rarg(x_16);
lean_inc(x_19);
x_20 = l_Lean_Name_append___main(x_2, x_19);
x_21 = l_Lean_Environment_contains(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_19);
x_22 = l_Lean_Elab_logUnknownDecl___rarg(x_16, x_20, x_8, x_9);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
x_6 = x_18;
x_9 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_6 = x_18;
x_9 = x_29;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_9, 0);
lean_dec(x_32);
x_33 = l_Lean_Name_append___main(x_3, x_19);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_box(0);
lean_ctor_set(x_9, 0, x_36);
x_6 = x_18;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = l_Lean_Name_append___main(x_3, x_19);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
x_6 = x_18;
x_7 = x_41;
x_9 = x_43;
goto _start;
}
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_addAlias(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'export', self export");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabExport___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = l_Lean_Elab_getNamespace___rarg(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_name_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_ctor_set(x_13, 0, x_12);
x_17 = l_Lean_Elab_getEnv___rarg(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_12);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_15, x_19, x_23, x_24, x_20, x_2, x_17);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_27, 0);
x_31 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_30, x_29);
lean_ctor_set(x_27, 0, x_31);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_27, 2);
x_36 = lean_ctor_get(x_27, 3);
x_37 = lean_ctor_get(x_27, 4);
x_38 = lean_ctor_get(x_27, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_39 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_33, x_32);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
lean_ctor_set(x_25, 1, x_40);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_25, 1);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
x_50 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_43, x_42);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_12);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_array_get(x_5, x_4, x_57);
x_59 = l_Lean_Syntax_getArgs___rarg(x_58);
lean_dec(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_15, x_53, x_59, x_60, x_56, x_2, x_55);
lean_dec(x_59);
lean_dec(x_53);
lean_dec(x_15);
lean_dec(x_11);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 5);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
x_72 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_65, x_63);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 6, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
lean_ctor_set(x_73, 2, x_67);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_69);
lean_ctor_set(x_73, 5, x_70);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_12);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_15);
lean_dec(x_11);
x_75 = l_Lean_Elab_elabExport___closed__2;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_75);
return x_13;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_13, 0);
x_77 = lean_ctor_get(x_13, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_13);
x_78 = lean_name_dec_eq(x_11, x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_12);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Elab_getEnv___rarg(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_box(0);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_array_get(x_5, x_4, x_86);
x_88 = l_Lean_Syntax_getArgs___rarg(x_87);
lean_dec(x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_76, x_81, x_88, x_89, x_85, x_2, x_84);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_11);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_91, 5);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
x_101 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_94, x_92);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 6, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
lean_ctor_set(x_102, 2, x_96);
lean_ctor_set(x_102, 3, x_97);
lean_ctor_set(x_102, 4, x_98);
lean_ctor_set(x_102, 5, x_99);
if (lean_is_scalar(x_93)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_93;
}
lean_ctor_set(x_103, 0, x_12);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_76);
lean_dec(x_11);
x_104 = l_Lean_Elab_elabExport___closed__2;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_77);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_106 = lean_ctor_get(x_9, 0);
x_107 = lean_ctor_get(x_9, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_9);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_getNamespace___rarg(x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_name_dec_eq(x_106, x_111);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_112);
x_116 = l_Lean_Elab_getEnv___rarg(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_108);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_box(0);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_array_get(x_5, x_4, x_122);
x_124 = l_Lean_Syntax_getArgs___rarg(x_123);
lean_dec(x_123);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_106, x_111, x_117, x_124, x_125, x_121, x_2, x_120);
lean_dec(x_124);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_106);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_136 = x_127;
} else {
 lean_dec_ref(x_127);
 x_136 = lean_box(0);
}
x_137 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_130, x_128);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 6, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_131);
lean_ctor_set(x_138, 2, x_132);
lean_ctor_set(x_138, 3, x_133);
lean_ctor_set(x_138, 4, x_134);
lean_ctor_set(x_138, 5, x_135);
if (lean_is_scalar(x_129)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_129;
}
lean_ctor_set(x_139, 0, x_108);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_111);
lean_dec(x_106);
x_140 = l_Lean_Elab_elabExport___closed__2;
if (lean_is_scalar(x_113)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_113;
 lean_ctor_set_tag(x_141, 1);
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_112);
return x_141;
}
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_9);
if (x_142 == 0)
{
return x_9;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_9, 0);
x_144 = lean_ctor_get(x_9, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_9);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabExport(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabExport");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabExport___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_export___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_7);
x_17 = lean_box(0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_5, 5);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 4);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_18, 4, x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_5, 5, x_26);
x_27 = lean_box(0);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
x_36 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_7, 1, x_32);
lean_ctor_set(x_7, 0, x_1);
x_37 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_7);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_5, 5, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_3, 0, x_39);
return x_3;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_18, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 7);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_45);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 8, 1);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_46);
lean_ctor_set(x_52, 6, x_47);
lean_ctor_set(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_5, 5, x_53);
x_54 = lean_box(0);
lean_ctor_set(x_3, 0, x_54);
return x_3;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
x_57 = lean_ctor_get(x_5, 2);
x_58 = lean_ctor_get(x_5, 3);
x_59 = lean_ctor_get(x_5, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_61 = x_7;
} else {
 lean_dec_ref(x_7);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_18, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_18, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_18, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 7);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_71 = x_18;
} else {
 lean_dec_ref(x_18);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_61;
}
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_66);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 8, 1);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_67);
lean_ctor_set(x_73, 6, x_68);
lean_ctor_set(x_73, 7, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*8, x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_55);
lean_ctor_set(x_75, 1, x_56);
lean_ctor_set(x_75, 2, x_57);
lean_ctor_set(x_75, 3, x_58);
lean_ctor_set(x_75, 4, x_59);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_3, 1, x_75);
lean_ctor_set(x_3, 0, x_76);
return x_3;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_78 = lean_ctor_get(x_77, 5);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_78);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 4);
lean_inc(x_93);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_94 = x_77;
} else {
 lean_dec_ref(x_77);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_88, 7);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_88, sizeof(void*)*8);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 x_106 = x_88;
} else {
 lean_dec_ref(x_88);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_101);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 8, 1);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_102);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_94;
}
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_91);
lean_ctor_set(x_110, 3, x_92);
lean_ctor_set(x_110, 4, x_93);
lean_ctor_set(x_110, 5, x_109);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
lean_object* l_Lean_Elab_addOpenDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_addOpenDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_addOpenDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_Syntax_getId___rarg(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_resolveNamespace(x_14, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_20, x_5, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_21, 0, x_18);
x_24 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_24;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_29;
x_4 = x_26;
x_6 = x_28;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_36, x_5, x_34);
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
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_42;
x_4 = x_38;
x_6 = x_41;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_Elab_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs___rarg(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(x_9, x_8, x_6, x_10, x_2, x_3);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_elabOpenSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenSimple(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_14 = lean_array_fget(x_3, x_4);
x_15 = l_Lean_Syntax_getId___rarg(x_14);
lean_inc(x_15);
x_16 = l_Lean_Name_append___main(x_1, x_15);
x_17 = l_Lean_Elab_getEnv___rarg(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
x_21 = l_Lean_Environment_contains(x_19, x_16);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_15);
x_22 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_16, x_6, x_17);
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_20);
x_25 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_25;
x_5 = x_24;
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_30;
x_5 = x_27;
x_7 = x_29;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_16);
x_33 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_32, x_6, x_17);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_33, 0, x_20);
x_36 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_36;
x_5 = x_35;
x_7 = x_33;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_41;
x_5 = x_38;
x_7 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Environment_contains(x_43, x_16);
lean_dec(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_15);
x_48 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_16, x_6, x_46);
lean_dec(x_14);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_53;
x_5 = x_49;
x_7 = x_52;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_15);
lean_ctor_set(x_55, 1, x_16);
x_56 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_55, x_6, x_46);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_61;
x_5 = x_57;
x_7 = x_60;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_elabOpenOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_5, x_4, x_13);
x_15 = l_Lean_Syntax_getArgs___rarg(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_11, x_16, x_15, x_6, x_12, x_2, x_9);
lean_dec(x_15);
lean_dec(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_array_get(x_5, x_4, x_22);
x_24 = l_Lean_Syntax_getArgs___rarg(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_18, x_25, x_24, x_6, x_20, x_2, x_21);
lean_dec(x_24);
lean_dec(x_18);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabOpenOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenOnly(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_fget(x_4, x_5);
x_16 = l_Lean_Syntax_getId___rarg(x_15);
lean_inc(x_16);
x_17 = l_Lean_Name_append___main(x_1, x_16);
x_18 = l_Lean_Environment_contains(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
x_19 = l_Lean_Elab_logUnknownDecl___rarg(x_15, x_17, x_7, x_8);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
x_23 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_23;
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_28;
x_8 = x_27;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_15);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_8, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_box(0);
lean_ctor_set(x_8, 0, x_33);
x_34 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_34;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_6);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_40;
x_6 = x_37;
x_8 = x_39;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_elabOpenHiding(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = l_Lean_Elab_getEnv___rarg(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_array_get(x_5, x_4, x_16);
lean_ctor_set(x_13, 0, x_12);
x_18 = lean_box(0);
x_19 = l_Lean_Syntax_getArgs___rarg(x_17);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_11, x_15, x_20, x_19, x_6, x_18, x_2, x_13);
lean_dec(x_19);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_21, 0, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_24, x_2, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_26);
x_30 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_29, x_2, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_array_get(x_5, x_4, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_box(0);
x_37 = l_Lean_Syntax_getArgs___rarg(x_34);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_11, x_31, x_38, x_37, x_6, x_36, x_2, x_35);
lean_dec(x_37);
lean_dec(x_31);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_40);
x_45 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_44, x_2, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_9);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_getEnv___rarg(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_array_get(x_5, x_4, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_52);
x_57 = lean_box(0);
x_58 = l_Lean_Syntax_getArgs___rarg(x_55);
lean_dec(x_55);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_46, x_51, x_59, x_58, x_6, x_57, x_2, x_56);
lean_dec(x_58);
lean_dec(x_51);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_61);
x_66 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_65, x_2, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_9);
if (x_67 == 0)
{
return x_9;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_9, 0);
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_9);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_elabOpenHiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenHiding(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_5);
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getIdAt___rarg(x_14, x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getIdAt___rarg(x_14, x_17);
x_19 = l_Lean_Name_append___main(x_1, x_16);
x_20 = l_Lean_Elab_getEnv___rarg(x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
x_24 = l_Lean_Environment_contains(x_22, x_19);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_18);
x_25 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_19, x_6, x_20);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_25, 0, x_23);
x_28 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_28;
x_5 = x_27;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_33;
x_5 = x_30;
x_7 = x_32;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_19);
x_36 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_35, x_6, x_20);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_36, 0, x_23);
x_39 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_39;
x_5 = x_38;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_44;
x_5 = x_41;
x_7 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Environment_contains(x_46, x_19);
lean_dec(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
x_51 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_19, x_6, x_49);
lean_dec(x_14);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_56;
x_5 = x_52;
x_7 = x_55;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_18);
lean_ctor_set(x_58, 1, x_19);
x_59 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_58, x_6, x_49);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_48);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_64;
x_5 = x_60;
x_7 = x_63;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_elabOpenRenaming(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_5, x_4, x_13);
x_15 = l_Lean_Syntax_getArgs___rarg(x_14);
lean_dec(x_14);
x_16 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_11, x_13, x_15, x_6, x_12, x_2, x_9);
lean_dec(x_15);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean_dec(x_22);
x_24 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_17, x_21, x_23, x_6, x_19, x_2, x_20);
lean_dec(x_23);
lean_dec(x_17);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabOpenRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenRenaming(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_asNode___rarg(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_11 = lean_name_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_13 = lean_name_dec_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_15 = lean_name_dec_eq(x_9, x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_elabOpenRenaming(x_8, x_2, x_3);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Elab_elabOpenHiding(x_8, x_2, x_3);
lean_dec(x_8);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = l_Lean_Elab_elabOpenOnly(x_8, x_2, x_3);
lean_dec(x_8);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = l_Lean_Elab_elabOpenSimple(x_8, x_2, x_3);
lean_dec(x_8);
return x_19;
}
}
}
lean_object* l_Lean_Elab_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpen(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabOpen");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabOpen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_7);
x_17 = lean_box(0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_5, 5);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 5);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_18, 5, x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_5, 5, x_26);
x_27 = lean_box(0);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
x_36 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_7, 1, x_33);
lean_ctor_set(x_7, 0, x_1);
x_37 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_7);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_5, 5, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_3, 0, x_39);
return x_3;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_18, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 7);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_46);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 8, 1);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_45);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set(x_52, 6, x_47);
lean_ctor_set(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_5, 5, x_53);
x_54 = lean_box(0);
lean_ctor_set(x_3, 0, x_54);
return x_3;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
x_57 = lean_ctor_get(x_5, 2);
x_58 = lean_ctor_get(x_5, 3);
x_59 = lean_ctor_get(x_5, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_61 = x_7;
} else {
 lean_dec_ref(x_7);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_18, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_18, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_18, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 7);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_71 = x_18;
} else {
 lean_dec_ref(x_18);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_61;
}
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_67);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 8, 1);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_66);
lean_ctor_set(x_73, 5, x_72);
lean_ctor_set(x_73, 6, x_68);
lean_ctor_set(x_73, 7, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*8, x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_55);
lean_ctor_set(x_75, 1, x_56);
lean_ctor_set(x_75, 2, x_57);
lean_ctor_set(x_75, 3, x_58);
lean_ctor_set(x_75, 4, x_59);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_3, 1, x_75);
lean_ctor_set(x_3, 0, x_76);
return x_3;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_78 = lean_ctor_get(x_77, 5);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_78);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 4);
lean_inc(x_93);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_94 = x_77;
} else {
 lean_dec_ref(x_77);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_88, 7);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_88, sizeof(void*)*8);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 x_106 = x_88;
} else {
 lean_dec_ref(x_88);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_102);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 8, 1);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 5, x_107);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_94;
}
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_91);
lean_ctor_set(x_110, 3, x_92);
lean_ctor_set(x_110, 4, x_93);
lean_ctor_set(x_110, 5, x_109);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
lean_object* _init_l_Lean_Elab_addUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe named '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_addUniverse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared in this Scope");
return x_1;
}
}
lean_object* l_Lean_Elab_addUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getId___rarg(x_1);
x_5 = l_Lean_Elab_getUniverses___rarg(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_4);
x_13 = l_Lean_Elab_addUniverse___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Elab_addUniverse___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_Elab_logError___rarg(x_1, x_16, x_2, x_5);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_18);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_4);
x_26 = l_Lean_Elab_addUniverse___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_Elab_addUniverse___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Elab_logError___rarg(x_1, x_29, x_2, x_21);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_addUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_addUniverse(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Elab_addUniverse(x_7, x_2, x_3);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabUniverse(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabUniverse");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabUniverse___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_Elab_addUniverse(x_13, x_5, x_6);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
x_18 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_18;
x_4 = x_16;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_24;
x_4 = x_20;
x_6 = x_23;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs___rarg(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(x_6, x_8, x_9, x_10, x_2, x_3);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_elabUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabUniverses(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabUniverses");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabUniverses___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabInitQuot___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_getEnv___rarg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_box(4);
x_8 = lean_add_decl(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Elab_logElabException(x_10, x_1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Elab_setEnv(x_12, x_1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_box(4);
x_19 = lean_add_decl(x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_logElabException(x_21, x_1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Elab_setEnv(x_23, x_1, x_17);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabInitQuot___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabInitQuot___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabInitQuot___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabInitQuot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_elabInitQuot(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabInitQuot");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabInitQuot___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_runIOUnsafe___rarg(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabVariable(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabVariable");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabVariable___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_1, x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Nat_repr(x_7);
x_10 = l_Prod_HasRepr___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_8);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = l_Option_HasRepr___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_12, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_6);
lean_dec(x_6);
return x_20;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; 
x_21 = l_String_splitAux___main___closed__1;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = 0;
x_25 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_24, x_23);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Nat_repr(x_26);
x_29 = l_Prod_HasRepr___rarg___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_List_reprAux___main___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_27);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = l_Option_HasRepr___rarg___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_25);
lean_dec(x_25);
return x_38;
}
}
}
}
lean_object* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_elabResolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveName(x_8, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_getPosition(x_13, x_2, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_12);
x_17 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Nat_repr(x_18);
x_21 = l_Sigma_HasRepr___rarg___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_List_reprAux___main___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_repr(x_19);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Sigma_HasRepr___rarg___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_String_Iterator_HasRepr___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_17);
lean_dec(x_17);
x_32 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_runIOUnsafe___rarg(x_32, x_2, x_14);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_12);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_11);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Nat_repr(x_46);
x_49 = l_Sigma_HasRepr___rarg___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_List_reprAux___main___rarg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Nat_repr(x_47);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = l_Sigma_HasRepr___rarg___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_String_Iterator_HasRepr___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_45);
lean_dec(x_45);
x_60 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = l_Lean_Elab_runIOUnsafe___rarg(x_60, x_2, x_44);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_box(0);
x_74 = l_Lean_Elab_getPosition(x_73, x_2, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_69);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l_Nat_repr(x_80);
x_83 = l_Sigma_HasRepr___rarg___closed__1;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = l_List_reprAux___main___rarg___closed__1;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Nat_repr(x_81);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = l_Sigma_HasRepr___rarg___closed__2;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_String_Iterator_HasRepr___closed__2;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_79);
lean_dec(x_79);
x_94 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_94, 0, x_93);
x_95 = l_Lean_Elab_runIOUnsafe___rarg(x_94, x_2, x_78);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_71);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_elabResolveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabResolveName(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabResolveName");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabResolveName___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabPreTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_runIOUnsafe___rarg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = x_7;
lean_inc(x_2);
x_14 = l_Lean_Elab_toPreTerm(x_13, x_2, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_12);
x_17 = lean_expr_dbg_to_string(x_16);
lean_dec(x_16);
x_18 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_runIOUnsafe___rarg(x_18, x_2, x_14);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_expr_dbg_to_string(x_28);
lean_dec(x_28);
x_32 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_runIOUnsafe___rarg(x_32, x_2, x_30);
lean_dec(x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_39 = x_33;
} else {
 lean_dec_ref(x_33);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec(x_9);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = x_7;
lean_inc(x_2);
x_49 = l_Lean_Elab_toPreTerm(x_48, x_2, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_expr_dbg_to_string(x_50);
lean_dec(x_50);
x_55 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = l_Lean_Elab_runIOUnsafe___rarg(x_55, x_2, x_53);
lean_dec(x_2);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_49, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_66 = x_49;
} else {
 lean_dec_ref(x_49);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_7);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
return x_9;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l_Lean_Elab_elabPreTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabPreTerm(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabPreTerm");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabPreTerm___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_IO_print___at_Lean_Elab_elabElab___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
x_6 = lean_io_prim_put_str(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_println___at_Lean_Elab_elabElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at_Lean_Elab_elabElab___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_io_prim_put_str(x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_io_prim_put_str(x_12, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* _init_l_Lean_Elab_elabElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to elaborate syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabElab___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabElab(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_4, x_7);
x_9 = x_8;
x_10 = 0;
lean_inc(x_2);
x_11 = l_Lean_Elab_elabTermAux___main(x_9, x_5, x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_expr_dbg_to_string(x_29);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = l_Lean_Elab_runIOUnsafe___rarg(x_31, x_2, x_11);
lean_dec(x_2);
return x_32;
}
else
{
x_15 = x_14;
goto block_28;
}
block_28:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
x_16 = lean_alloc_closure((void*)(l_IO_println___at_Lean_Elab_elabElab___spec__1), 2, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = l_Lean_Elab_runIOUnsafe___rarg(x_16, x_2, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Elab_elabElab___closed__2;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Elab_elabElab___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
lean_dec(x_33);
x_50 = lean_expr_dbg_to_string(x_49);
lean_dec(x_49);
x_51 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_runIOUnsafe___rarg(x_51, x_2, x_36);
lean_dec(x_2);
return x_52;
}
else
{
x_37 = x_35;
goto block_48;
}
block_48:
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_37);
x_38 = lean_alloc_closure((void*)(l_IO_println___at_Lean_Elab_elabElab___spec__1), 2, 1);
lean_closure_set(x_38, 0, x_33);
x_39 = l_Lean_Elab_runIOUnsafe___rarg(x_38, x_2, x_36);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Elab_elabElab___closed__2;
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_41;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Elab_elabElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabElab(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabElab");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabElab___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabMixfix___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_Elab_elabMixfix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_elabMixfix___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_elabMixfix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabMixfix(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabMixfix");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabMixfix___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabReserve___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_Elab_elabReserve(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_elabReserve___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_elabReserve___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabReserve(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabReserve");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabReserve___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_reserve___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabNotation___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_Elab_elabNotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_elabNotation___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_elabNotation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabNotation(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNotation");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabNotation___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_notation___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elaborator_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Basic(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elaborator_Command(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_Alias(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_ResolveName(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_Term(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabNamespace(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabSection(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Elab_elabEnd___closed__1 = _init_l_Lean_Elab_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__1);
l_Lean_Elab_elabEnd___closed__2 = _init_l_Lean_Elab_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__2);
l_Lean_Elab_elabEnd___closed__3 = _init_l_Lean_Elab_elabEnd___closed__3();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__3);
l_Lean_Elab_elabEnd___closed__4 = _init_l_Lean_Elab_elabEnd___closed__4();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__4);
l_Lean_Elab_elabEnd___closed__5 = _init_l_Lean_Elab_elabEnd___closed__5();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__5);
l_Lean_Elab_elabEnd___closed__6 = _init_l_Lean_Elab_elabEnd___closed__6();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__6);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabEnd(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Elab_elabExport___closed__1 = _init_l_Lean_Elab_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_elabExport___closed__1);
l_Lean_Elab_elabExport___closed__2 = _init_l_Lean_Elab_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_elabExport___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabExport(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabOpen(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Elab_addUniverse___closed__1 = _init_l_Lean_Elab_addUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_addUniverse___closed__1);
l_Lean_Elab_addUniverse___closed__2 = _init_l_Lean_Elab_addUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_addUniverse___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabUniverse(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabUniverses(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabInitQuot(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabVariable(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabResolveName(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabPreTerm(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Elab_elabElab___closed__1 = _init_l_Lean_Elab_elabElab___closed__1();
lean_mark_persistent(l_Lean_Elab_elabElab___closed__1);
l_Lean_Elab_elabElab___closed__2 = _init_l_Lean_Elab_elabElab___closed__2();
lean_mark_persistent(l_Lean_Elab_elabElab___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabElab(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabMixfix(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabReserve(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabNotation(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
