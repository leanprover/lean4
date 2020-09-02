// Lean compiler output
// Module: Lean.Elab.Declaration
// Imports: Init Lean.Util.CollectLevelParams Lean.Elab.DeclUtil Lean.Elab.Definition Lean.Elab.Inductive Lean.Elab.Structure Lean.Elab.MutualDef
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
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_elabStructure___closed__11;
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__5;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___closed__1;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__3;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
uint8_t l___private_Lean_Elab_Declaration_5__isMutualDef(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutualDef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclIdNamespace_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_elabSection___closed__2;
uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__4;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
extern lean_object* l___private_Lean_Elab_Command_9__addNamespace___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_elabSection___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10;
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__classInductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__7;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
extern lean_object* l_Lean_Elab_Command_isDefLike___closed__4;
extern lean_object* l_Lean_Elab_Command_isDefLike___closed__8;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_5__isMutualDef___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_isDefLike___closed__2;
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1(lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2;
lean_object* l_Lean_Elab_expandMacro_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2;
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_isDefLike___closed__9;
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7;
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_4__elabMutualInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___rarg(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_3__isMutualInductive___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2;
lean_object* l_Lean_Elab_Command_elabMutual___closed__2;
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l___private_Lean_Elab_Declaration_3__isMutualInductive(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualDef___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1;
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
uint8_t l___private_Lean_Elab_Declaration_6__isMutualPreambleCommand(lean_object*);
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__1;
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Command_elabMutual(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3;
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
extern lean_object* l_Lean_Elab_Command_isDefLike___closed__6;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__9;
lean_object* l_Lean_Elab_Command_elabMutual___closed__3;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__6;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_4__getVarDecls(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5;
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_4__elabMutualInductive(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallUsedOnly___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__5;
lean_object* l_Lean_Elab_Command_mkDefView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6;
lean_object* l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___closed__1;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__4;
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* l_Lean_Meta_mkForallUsedOnly___at_Lean_Elab_Command_elabAxiom___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__6;
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2;
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
lean_object* l___private_Lean_Elab_Declaration_6__isMutualPreambleCommand___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Command_elabMutual___closed__1;
lean_object* l_Lean_Elab_Command_expandDeclIdNamespace_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_expandDeclIdCore(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_4 = x_2;
} else {
 lean_dec_ref(x_2);
 x_4 = lean_box(0);
}
x_5 = l_Lean_extractMacroScopes(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_10 = x_5;
} else {
 lean_dec_ref(x_5);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_13 = x_29;
goto block_27;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = lean_name_mk_string(x_14, x_12);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(0, 4, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_9);
x_17 = l_Lean_MacroScopesView_review(x_16);
x_18 = l_Lean_Syntax_isIdent(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lean_mkIdentFrom(x_1, x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_setArg(x_1, x_20, x_19);
if (lean_is_scalar(x_4)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_4;
}
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_mkIdentFrom(x_1, x_17);
lean_dec(x_1);
if (lean_is_scalar(x_4)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_4;
}
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_box(0);
return x_30;
}
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("axiom");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("classInductive");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_expandDeclNamespace_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = l_Lean_Elab_Command_isDefLike___closed__2;
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Command_isDefLike___closed__4;
x_11 = lean_name_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Command_isDefLike___closed__6;
x_13 = lean_name_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Command_isDefLike___closed__8;
x_15 = lean_name_eq(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
x_17 = lean_name_eq(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_19 = lean_name_eq(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8;
x_21 = lean_name_eq(x_7, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Command_isDefLike___closed__9;
x_23 = lean_name_eq(x_7, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10;
x_25 = lean_name_eq(x_7, x_24);
lean_dec(x_7);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(2u);
x_28 = l_Lean_Syntax_getArg(x_6, x_27);
x_29 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = l_Lean_Syntax_setArg(x_6, x_27, x_33);
x_35 = l_Lean_Syntax_setArg(x_1, x_5, x_34);
lean_ctor_set(x_31, 1, x_35);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = l_Lean_Syntax_setArg(x_6, x_27, x_37);
x_39 = l_Lean_Syntax_setArg(x_1, x_5, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Syntax_setArg(x_6, x_27, x_43);
x_46 = l_Lean_Syntax_setArg(x_1, x_5, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_7);
x_49 = l_Lean_Syntax_getArg(x_6, x_5);
x_50 = l_Lean_Syntax_isNone(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_49, x_51);
x_53 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_1);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 1);
x_58 = l_Lean_Syntax_setArg(x_49, x_51, x_57);
x_59 = l_Lean_Syntax_setArg(x_6, x_5, x_58);
x_60 = l_Lean_Syntax_setArg(x_1, x_5, x_59);
lean_ctor_set(x_55, 1, x_60);
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = l_Lean_Syntax_setArg(x_49, x_51, x_62);
x_64 = l_Lean_Syntax_setArg(x_6, x_5, x_63);
x_65 = l_Lean_Syntax_setArg(x_1, x_5, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_53, 0, x_66);
return x_53;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_53, 0);
lean_inc(x_67);
lean_dec(x_53);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Syntax_setArg(x_49, x_51, x_69);
x_72 = l_Lean_Syntax_setArg(x_6, x_5, x_71);
x_73 = l_Lean_Syntax_setArg(x_1, x_5, x_72);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_1);
x_76 = lean_box(0);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_7);
x_77 = l_Lean_Syntax_getArg(x_6, x_5);
x_78 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 1);
x_83 = l_Lean_Syntax_setArg(x_6, x_5, x_82);
x_84 = l_Lean_Syntax_setArg(x_1, x_5, x_83);
lean_ctor_set(x_80, 1, x_84);
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Syntax_setArg(x_6, x_5, x_86);
x_88 = l_Lean_Syntax_setArg(x_1, x_5, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_78, 0, x_89);
return x_78;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Syntax_setArg(x_6, x_5, x_92);
x_95 = l_Lean_Syntax_setArg(x_1, x_5, x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_7);
x_98 = l_Lean_Syntax_getArg(x_6, x_5);
x_99 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 1);
x_104 = l_Lean_Syntax_setArg(x_6, x_5, x_103);
x_105 = l_Lean_Syntax_setArg(x_1, x_5, x_104);
lean_ctor_set(x_101, 1, x_105);
return x_99;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = l_Lean_Syntax_setArg(x_6, x_5, x_107);
x_109 = l_Lean_Syntax_setArg(x_1, x_5, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_99, 0, x_110);
return x_99;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = l_Lean_Syntax_setArg(x_6, x_5, x_113);
x_116 = l_Lean_Syntax_setArg(x_1, x_5, x_115);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_7);
x_119 = l_Lean_Syntax_getArg(x_6, x_5);
x_120 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_120;
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 1);
x_125 = l_Lean_Syntax_setArg(x_6, x_5, x_124);
x_126 = l_Lean_Syntax_setArg(x_1, x_5, x_125);
lean_ctor_set(x_122, 1, x_126);
return x_120;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_122, 0);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_122);
x_129 = l_Lean_Syntax_setArg(x_6, x_5, x_128);
x_130 = l_Lean_Syntax_setArg(x_1, x_5, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_120, 0, x_131);
return x_120;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_120, 0);
lean_inc(x_132);
lean_dec(x_120);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Syntax_setArg(x_6, x_5, x_134);
x_137 = l_Lean_Syntax_setArg(x_1, x_5, x_136);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_133);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_7);
x_140 = l_Lean_Syntax_getArg(x_6, x_5);
x_141 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_141;
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 1);
x_146 = l_Lean_Syntax_setArg(x_6, x_5, x_145);
x_147 = l_Lean_Syntax_setArg(x_1, x_5, x_146);
lean_ctor_set(x_143, 1, x_147);
return x_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_143, 0);
x_149 = lean_ctor_get(x_143, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_143);
x_150 = l_Lean_Syntax_setArg(x_6, x_5, x_149);
x_151 = l_Lean_Syntax_setArg(x_1, x_5, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_141, 0, x_152);
return x_141;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_141, 0);
lean_inc(x_153);
lean_dec(x_141);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = l_Lean_Syntax_setArg(x_6, x_5, x_155);
x_158 = l_Lean_Syntax_setArg(x_1, x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_7);
x_161 = l_Lean_Syntax_getArg(x_6, x_5);
x_162 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_162;
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_164, 1);
x_167 = l_Lean_Syntax_setArg(x_6, x_5, x_166);
x_168 = l_Lean_Syntax_setArg(x_1, x_5, x_167);
lean_ctor_set(x_164, 1, x_168);
return x_162;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_164, 0);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_164);
x_171 = l_Lean_Syntax_setArg(x_6, x_5, x_170);
x_172 = l_Lean_Syntax_setArg(x_1, x_5, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_162, 0, x_173);
return x_162;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_162, 0);
lean_inc(x_174);
lean_dec(x_162);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = l_Lean_Syntax_setArg(x_6, x_5, x_176);
x_179 = l_Lean_Syntax_setArg(x_1, x_5, x_178);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_7);
x_182 = l_Lean_Syntax_getArg(x_6, x_5);
x_183 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_183;
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_185, 1);
x_188 = l_Lean_Syntax_setArg(x_6, x_5, x_187);
x_189 = l_Lean_Syntax_setArg(x_1, x_5, x_188);
lean_ctor_set(x_185, 1, x_189);
return x_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_185, 0);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_185);
x_192 = l_Lean_Syntax_setArg(x_6, x_5, x_191);
x_193 = l_Lean_Syntax_setArg(x_1, x_5, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set(x_183, 0, x_194);
return x_183;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_195 = lean_ctor_get(x_183, 0);
lean_inc(x_195);
lean_dec(x_183);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = l_Lean_Syntax_setArg(x_6, x_5, x_197);
x_200 = l_Lean_Syntax_setArg(x_1, x_5, x_199);
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_196);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
x_203 = l_Lean_Syntax_getArg(x_6, x_5);
x_204 = l_Lean_Elab_Command_expandDeclIdNamespace_x3f(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_204;
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_206, 1);
x_209 = l_Lean_Syntax_setArg(x_6, x_5, x_208);
x_210 = l_Lean_Syntax_setArg(x_1, x_5, x_209);
lean_ctor_set(x_206, 1, x_210);
return x_204;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_206, 0);
x_212 = lean_ctor_get(x_206, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_206);
x_213 = l_Lean_Syntax_setArg(x_6, x_5, x_212);
x_214 = l_Lean_Syntax_setArg(x_1, x_5, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_204, 0, x_215);
return x_204;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_216 = lean_ctor_get(x_204, 0);
lean_inc(x_216);
lean_dec(x_204);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_219 = x_216;
} else {
 lean_dec_ref(x_216);
 x_219 = lean_box(0);
}
x_220 = l_Lean_Syntax_setArg(x_6, x_5, x_218);
x_221 = l_Lean_Syntax_setArg(x_1, x_5, x_220);
if (lean_is_scalar(x_219)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_219;
}
lean_ctor_set(x_222, 0, x_217);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
}
}
}
lean_object* l_Lean_Meta_mkForallUsedOnly___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_31 = lean_st_ref_take(x_8, x_13);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_32, 2);
lean_dec(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_32, 2, x_36);
x_37 = lean_st_ref_set(x_8, x_32, x_33);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_6, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_8, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = l_Std_HashMap_inhabited___closed__1;
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_48);
x_50 = 0;
x_51 = 1;
x_52 = l_Lean_MetavarContext_MkBinding_mkBinding(x_50, x_47, x_1, x_2, x_51, x_50, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_st_ref_take(x_8, x_45);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_58, 1);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_56);
x_62 = lean_st_ref_set(x_8, x_58, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_55, x_5, x_6, x_7, x_8, x_63);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_54);
x_15 = x_64;
goto block_30;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_67);
x_15 = x_68;
goto block_30;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_st_ref_set(x_8, x_71, x_59);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_55, x_5, x_6, x_7, x_8, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_54);
lean_ctor_set(x_77, 1, x_75);
x_15 = x_77;
goto block_30;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_52, 1);
lean_inc(x_78);
lean_dec(x_52);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_79, x_5, x_6, x_7, x_8, x_45);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_take(x_8, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_84, 1);
lean_dec(x_87);
lean_ctor_set(x_84, 1, x_80);
x_88 = lean_st_ref_set(x_8, x_84, x_85);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_91 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_90, x_5, x_6, x_7, x_8, x_89);
x_15 = x_91;
goto block_30;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_84, 0);
x_93 = lean_ctor_get(x_84, 2);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_84);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_80);
lean_ctor_set(x_94, 2, x_93);
x_95 = lean_st_ref_set(x_8, x_94, x_85);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_98 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_97, x_5, x_6, x_7, x_8, x_96);
x_15 = x_98;
goto block_30;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; 
x_99 = lean_ctor_get(x_32, 0);
x_100 = lean_ctor_get(x_32, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_32);
x_101 = l_Lean_TraceState_Inhabited___closed__1;
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_101);
x_103 = lean_st_ref_set(x_8, x_102, x_33);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_get(x_6, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_st_ref_get(x_8, x_107);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_5, 1);
lean_inc(x_113);
x_114 = l_Std_HashMap_inhabited___closed__1;
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_112);
lean_ctor_set(x_115, 2, x_114);
x_116 = 0;
x_117 = 1;
x_118 = l_Lean_MetavarContext_MkBinding_mkBinding(x_116, x_113, x_1, x_2, x_117, x_116, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_st_ref_take(x_8, x_111);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 2);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 3, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_122);
lean_ctor_set(x_129, 2, x_127);
x_130 = lean_st_ref_set(x_8, x_129, x_125);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_121, x_5, x_6, x_7, x_8, x_131);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_120);
lean_ctor_set(x_135, 1, x_133);
x_15 = x_135;
goto block_30;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_136 = lean_ctor_get(x_118, 1);
lean_inc(x_136);
lean_dec(x_118);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_137, x_5, x_6, x_7, x_8, x_111);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_st_ref_take(x_8, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 3, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_138);
lean_ctor_set(x_147, 2, x_145);
x_148 = lean_st_ref_set(x_8, x_147, x_143);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_151 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_150, x_5, x_6, x_7, x_8, x_149);
x_15 = x_151;
goto block_30;
}
}
block_30:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_1);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_2);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_st_ref_get(x_8, x_9);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 2);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_st_ref_take(x_8, x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = !lean_is_exclusive(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_162 = lean_ctor_get(x_159, 2);
lean_dec(x_162);
x_163 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_159, 2, x_163);
x_164 = lean_st_ref_set(x_8, x_159, x_160);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_157, x_3, x_4, x_5, x_6, x_7, x_8, x_165);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
lean_ctor_set(x_166, 0, x_153);
return x_166;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_153);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_159, 0);
x_172 = lean_ctor_get(x_159, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_159);
x_173 = l_Lean_TraceState_Inhabited___closed__1;
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_173);
x_175 = lean_st_ref_set(x_8, x_174, x_160);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_157, x_3, x_4, x_5, x_6, x_7, x_8, x_176);
lean_dec(x_5);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_153);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = 2;
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_19 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_2, x_17, x_16, x_18, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Elab_Term_elabType(x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_26 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_24, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_9);
x_28 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_9);
x_31 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_8, x_29, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_9);
x_34 = l_Lean_Meta_mkForallUsedOnly___at_Lean_Elab_Command_elabAxiom___spec__1(x_4, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_39 = l_Lean_Elab_Term_levelMVarToParam(x_37, x_38, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Command_mkDef_x3f___lambda__1___closed__1;
lean_inc(x_42);
x_44 = l_Lean_CollectLevelParams_main___main(x_42, x_43);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Elab_Command_sortDeclLevelParams(x_5, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_7, x_49, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_42);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_9);
lean_inc(x_55);
x_56 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_55, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_13);
x_58 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_55, x_9, x_10, x_11, x_12, x_13, x_14, x_57);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_61 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_2, x_60, x_16, x_18, x_13, x_14, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = 1;
x_64 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_2, x_63, x_16, x_18, x_13, x_14, x_62);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
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
lean_dec(x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_56);
if (x_73 == 0)
{
return x_56;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_56, 0);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_56);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
return x_34;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_34);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_31);
if (x_81 == 0)
{
return x_31;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_31, 0);
x_83 = lean_ctor_get(x_31, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_31);
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
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_26);
if (x_85 == 0)
{
return x_26;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_26, 0);
x_87 = lean_ctor_get(x_26, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_26);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_21);
if (x_89 == 0)
{
return x_21;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_21, 0);
x_91 = lean_ctor_get(x_21, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_21);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_19);
if (x_93 == 0)
{
return x_19;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_19, 0);
x_95 = lean_ctor_get(x_19, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_19);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Syntax_getArgs(x_1);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__1___boxed), 15, 7);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_6);
lean_closure_set(x_17, 6, x_7);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Term_withLevelNames___rarg(x_6, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Elab_expandDeclSig(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
x_16 = l_Lean_Elab_Command_expandDeclId(x_7, x_1, x_3, x_4, x_15);
lean_dec(x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2___boxed), 15, 7);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_19);
lean_closure_set(x_22, 3, x_12);
lean_closure_set(x_22, 4, x_14);
lean_closure_set(x_22, 5, x_20);
lean_closure_set(x_22, 6, x_2);
x_23 = lean_st_ref_get(x_4, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_Command_4__getVarDecls(x_24);
lean_dec(x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_22);
x_28 = l_Lean_Elab_Command_liftTermElabM___rarg(x_21, x_27, x_3, x_4, x_25);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_mkForallUsedOnly___at_Lean_Elab_Command_elabAxiom___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkForallUsedOnly___at_Lean_Elab_Command_elabAxiom___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabAxiom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabAxiom___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabAxiom(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' constructor in a 'private' inductive datatype");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' constructor in a 'private' inductive datatype");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = x_4;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_12 = lean_array_fget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_4, x_3, x_13);
x_28 = x_12;
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_28, x_29);
x_31 = l_Lean_Elab_Command_getRef(x_5, x_6, x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_replaceRef(x_28, x_32);
lean_dec(x_32);
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
x_37 = lean_ctor_get(x_5, 2);
x_38 = lean_ctor_get(x_5, 3);
x_39 = lean_ctor_get(x_5, 4);
x_40 = lean_ctor_get(x_5, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_39);
lean_ctor_set(x_41, 5, x_40);
lean_ctor_set(x_41, 6, x_34);
lean_inc(x_41);
x_42 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_30, x_41, x_6, x_33);
lean_dec(x_30);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_102; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_102 = l_Lean_Elab_Modifiers_isPrivate(x_43);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_Lean_Elab_Modifiers_isProtected(x_43);
if (x_103 == 0)
{
x_45 = x_44;
goto block_101;
}
else
{
uint8_t x_104; 
x_104 = l_Lean_Elab_Modifiers_isPrivate(x_1);
if (x_104 == 0)
{
x_45 = x_44;
goto block_101;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_43);
lean_dec(x_28);
x_105 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3;
x_106 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_105, x_41, x_6, x_44);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
x_15 = x_106;
goto block_27;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_15 = x_110;
goto block_27;
}
}
}
}
else
{
uint8_t x_111; 
x_111 = l_Lean_Elab_Modifiers_isPrivate(x_1);
if (x_111 == 0)
{
x_45 = x_44;
goto block_101;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_43);
lean_dec(x_28);
x_112 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6;
x_113 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_112, x_41, x_6, x_44);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
x_15 = x_113;
goto block_27;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_15 = x_117;
goto block_27;
}
}
}
block_101:
{
lean_object* x_46; 
lean_inc(x_41);
x_46 = l_Lean_Elab_Command_checkValidCtorModifier(x_43, x_41, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(2u);
x_49 = l_Lean_Syntax_getIdAt(x_28, x_48);
x_50 = l_Lean_Name_append___main(x_2, x_49);
x_51 = l_Lean_Syntax_getArg(x_28, x_48);
x_52 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_53 = l_Lean_Elab_Command_getRef(x_41, x_6, x_47);
lean_dec(x_41);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_replaceRef(x_51, x_54);
lean_dec(x_54);
lean_dec(x_51);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_57 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_57, 0, x_35);
lean_ctor_set(x_57, 1, x_36);
lean_ctor_set(x_57, 2, x_37);
lean_ctor_set(x_57, 3, x_38);
lean_ctor_set(x_57, 4, x_39);
lean_ctor_set(x_57, 5, x_40);
lean_ctor_set(x_57, 6, x_56);
x_58 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(x_52, x_50, x_57, x_6, x_55);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_unsigned_to_nat(3u);
x_62 = l_Lean_Syntax_getArg(x_28, x_61);
x_63 = l_Lean_Syntax_isNone(x_62);
lean_dec(x_62);
x_64 = lean_unsigned_to_nat(4u);
x_65 = l_Lean_Syntax_getArg(x_28, x_64);
x_66 = l_Lean_Elab_expandOptDeclSig(x_65);
lean_dec(x_65);
if (x_63 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = 1;
x_70 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_70, 0, x_28);
lean_ctor_set(x_70, 1, x_43);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*5, x_69);
lean_ctor_set(x_58, 0, x_70);
x_15 = x_58;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = 0;
x_74 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_74, 0, x_28);
lean_ctor_set(x_74, 1, x_43);
lean_ctor_set(x_74, 2, x_60);
lean_ctor_set(x_74, 3, x_71);
lean_ctor_set(x_74, 4, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*5, x_73);
lean_ctor_set(x_58, 0, x_74);
x_15 = x_58;
goto block_27;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_58, 0);
x_76 = lean_ctor_get(x_58, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_58);
x_77 = lean_unsigned_to_nat(3u);
x_78 = l_Lean_Syntax_getArg(x_28, x_77);
x_79 = l_Lean_Syntax_isNone(x_78);
lean_dec(x_78);
x_80 = lean_unsigned_to_nat(4u);
x_81 = l_Lean_Syntax_getArg(x_28, x_80);
x_82 = l_Lean_Elab_expandOptDeclSig(x_81);
lean_dec(x_81);
if (x_79 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = 1;
x_86 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_86, 0, x_28);
lean_ctor_set(x_86, 1, x_43);
lean_ctor_set(x_86, 2, x_75);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*5, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
x_15 = x_87;
goto block_27;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = 0;
x_91 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_91, 0, x_28);
lean_ctor_set(x_91, 1, x_43);
lean_ctor_set(x_91, 2, x_75);
lean_ctor_set(x_91, 3, x_88);
lean_ctor_set(x_91, 4, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*5, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_76);
x_15 = x_92;
goto block_27;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_43);
lean_dec(x_28);
x_93 = !lean_is_exclusive(x_58);
if (x_93 == 0)
{
x_15 = x_58;
goto block_27;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_58, 0);
x_95 = lean_ctor_get(x_58, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_58);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_15 = x_96;
goto block_27;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_28);
x_97 = !lean_is_exclusive(x_46);
if (x_97 == 0)
{
x_15 = x_46;
goto block_27;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_46, 0);
x_99 = lean_ctor_get(x_46, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_46);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_15 = x_100;
goto block_27;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_41);
lean_dec(x_28);
x_118 = !lean_is_exclusive(x_42);
if (x_118 == 0)
{
x_15 = x_42;
goto block_27;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_42, 0);
x_120 = lean_ctor_get(x_42, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_42);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_15 = x_121;
goto block_27;
}
}
block_27:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_14, x_3, x_20);
lean_dec(x_3);
x_3 = x_19;
x_4 = x_21;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_Elab_Command_checkValidInductiveModifier(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_expandOptDeclSig(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_getArg(x_2, x_3);
lean_inc(x_4);
x_16 = l_Lean_Elab_Command_expandDeclId(x_15, x_1, x_4, x_5, x_8);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
lean_dec(x_23);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = x_25;
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___boxed), 7, 4);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_20);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_26);
x_29 = x_28;
x_30 = lean_apply_3(x_29, x_4, x_5, x_18);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_33, 2, x_19);
lean_ctor_set(x_33, 3, x_20);
lean_ctor_set(x_33, 4, x_21);
lean_ctor_set(x_33, 5, x_13);
lean_ctor_set(x_33, 6, x_14);
lean_ctor_set(x_33, 7, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_19);
lean_ctor_set(x_36, 3, x_20);
lean_ctor_set(x_36, 4, x_21);
lean_ctor_set(x_36, 5, x_13);
lean_ctor_set(x_36, 6, x_14);
lean_ctor_set(x_36, 7, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Declaration_2__classInductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_1, x_2, x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_mkOptionalNode___closed__2;
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Elab_Command_elabInductiveViews(x_11, x_3, x_4, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_elabStructure___closed__11;
x_7 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_6);
x_8 = lean_unsigned_to_nat(2u);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_7, x_2, x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_mkOptionalNode___closed__2;
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Lean_Elab_Command_elabInductiveViews(x_13, x_3, x_4, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Command_9__addNamespace___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Elab_Command_expandDeclNamespace_x3f(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_inc(x_2);
x_8 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_7, x_2, x_3, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
lean_inc(x_12);
x_13 = l_Lean_Syntax_getKind(x_12);
x_14 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10;
x_19 = lean_name_eq(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8;
x_21 = lean_name_eq(x_13, x_20);
lean_dec(x_13);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_12);
x_22 = l_Lean_Elab_Command_isDefLike(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_9);
x_23 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_24 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_23, x_2, x_3, x_10);
lean_dec(x_3);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_2);
x_25 = l_Lean_Elab_Command_mkDefView(x_9, x_12, x_2, x_3, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Command_elabDefLike(x_26, x_2, x_3, x_27);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Elab_Command_elabStructure(x_9, x_12, x_2, x_3, x_10);
lean_dec(x_3);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_13);
x_34 = l_Lean_Elab_Command_elabClassInductive(x_9, x_12, x_2, x_3, x_10);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_13);
x_35 = l_Lean_Elab_Command_elabInductive(x_9, x_12, x_2, x_3, x_10);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
x_36 = l_Lean_Elab_Command_elabAxiom(x_9, x_12, x_2, x_3, x_10);
lean_dec(x_3);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_mkIdentFrom(x_1, x_42);
x_45 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_4);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_44);
x_50 = lean_array_push(x_49, x_44);
x_51 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Array_empty___closed__1;
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_array_push(x_54, x_43);
x_56 = lean_array_push(x_53, x_44);
x_57 = l_Lean_nullKind___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_60 = lean_array_push(x_59, x_58);
x_61 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_array_push(x_55, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_2, 4);
lean_inc(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_2, 4, x_68);
x_69 = l_Lean_Elab_Command_elabCommand___main(x_64, x_2, x_3, x_48);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_2, 0);
x_71 = lean_ctor_get(x_2, 1);
x_72 = lean_ctor_get(x_2, 2);
x_73 = lean_ctor_get(x_2, 3);
x_74 = lean_ctor_get(x_2, 4);
x_75 = lean_ctor_get(x_2, 5);
x_76 = lean_ctor_get(x_2, 6);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_2);
lean_inc(x_64);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_64);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
x_79 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_75);
lean_ctor_set(x_79, 6, x_76);
x_80 = l_Lean_Elab_Command_elabCommand___main(x_64, x_79, x_3, x_48);
return x_80;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_4 = x_14;
goto _start;
}
}
}
}
uint8_t l___private_Lean_Elab_Declaration_3__isMutualInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(x_1, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Declaration_3__isMutualInductive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_3__isMutualInductive(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_4__elabMutualInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_2, x_1, x_11);
x_13 = x_10;
x_14 = l_Lean_Syntax_getArg(x_13, x_11);
lean_inc(x_3);
x_15 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_14, x_3, x_4, x_5);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_16, x_19, x_18, x_3, x_4, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_add(x_1, x_18);
x_24 = x_21;
x_25 = lean_array_fset(x_12, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_5 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_4__elabMutualInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_4__elabMutualInductive___spec__1), 5, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = x_7;
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_apply_3(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_elabInductiveViews(x_10, x_2, x_3, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualDef___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_isDefLike(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
}
}
}
uint8_t l___private_Lean_Elab_Declaration_5__isMutualDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualDef___spec__1(x_1, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualDef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualDef___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Declaration_5__isMutualDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_5__isMutualDef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Declaration_6__isMutualPreambleCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
x_12 = lean_name_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2;
x_14 = lean_name_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2;
x_16 = lean_name_eq(x_2, x_15);
lean_dec(x_2);
return x_16;
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
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = 1;
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = 1;
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_Declaration_6__isMutualPreambleCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_6__isMutualPreambleCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Declaration_6__isMutualPreambleCommand(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_extract___rarg(x_1, x_8, x_2);
x_11 = l_Array_extract___rarg(x_1, x_2, x_3);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_7__splitMutualPreamble___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_7__splitMutualPreamble(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Command_elabSection___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__2;
x_2 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSection___closed__2;
x_2 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_2 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_2 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Declaration_7__splitMutualPreamble___main(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_nullKind;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Syntax_setArg(x_1, x_4, x_16);
x_18 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7;
x_19 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_13, x_13, x_7, x_18);
lean_dec(x_13);
x_20 = l_Lean_mkOptionalNode___closed__2;
x_21 = lean_array_push(x_20, x_17);
x_22 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_21, x_21, x_7, x_19);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8;
x_24 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_23, x_23, x_7, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_8, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_nullKind;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Syntax_setArg(x_1, x_4, x_31);
x_33 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7;
x_34 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_28, x_28, x_7, x_33);
lean_dec(x_28);
x_35 = l_Lean_mkOptionalNode___closed__2;
x_36 = lean_array_push(x_35, x_32);
x_37 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_36, x_36, x_7, x_34);
lean_dec(x_36);
x_38 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8;
x_39 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_38, x_38, x_7, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_7, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_7, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_6, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_7, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_environment_main_module(x_24);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_33);
lean_inc(x_12);
x_36 = l_Lean_Elab_expandMacro_x3f(x_2, x_12, x_35, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_take(x_7, x_32);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 3);
lean_dec(x_43);
lean_ctor_set(x_40, 3, x_38);
x_44 = lean_st_ref_set(x_7, x_40, x_41);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_array_push(x_16, x_12);
lean_ctor_set(x_5, 0, x_46);
x_4 = x_14;
x_8 = x_45;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_12);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_37, 0);
lean_inc(x_49);
lean_dec(x_37);
x_50 = lean_array_push(x_16, x_49);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_5, 1, x_52);
lean_ctor_set(x_5, 0, x_50);
x_4 = x_14;
x_8 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
x_56 = lean_ctor_get(x_40, 2);
x_57 = lean_ctor_get(x_40, 4);
x_58 = lean_ctor_get(x_40, 5);
x_59 = lean_ctor_get(x_40, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_60 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_38);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_58);
lean_ctor_set(x_60, 6, x_59);
x_61 = lean_st_ref_set(x_7, x_60, x_41);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_array_push(x_16, x_12);
lean_ctor_set(x_5, 0, x_63);
x_4 = x_14;
x_8 = x_62;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
lean_dec(x_17);
lean_dec(x_12);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_ctor_get(x_37, 0);
lean_inc(x_66);
lean_dec(x_37);
x_67 = lean_array_push(x_16, x_66);
x_68 = 1;
x_69 = lean_box(x_68);
lean_ctor_set(x_5, 1, x_69);
lean_ctor_set(x_5, 0, x_67);
x_4 = x_14;
x_8 = x_65;
goto _start;
}
}
}
else
{
lean_object* x_71; 
lean_free_object(x_5);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_71 = lean_ctor_get(x_36, 0);
lean_inc(x_71);
lean_dec(x_36);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_72, x_75, x_6, x_7, x_32);
lean_dec(x_72);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_6);
x_81 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___rarg(x_32);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_5);
x_88 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_8);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_7, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_7, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 3);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_6, 2);
lean_inc(x_99);
x_100 = lean_st_ref_get(x_7, x_97);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 4);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_environment_main_module(x_94);
x_105 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_89);
lean_ctor_set(x_105, 2, x_99);
lean_ctor_set(x_105, 3, x_103);
lean_inc(x_12);
x_106 = l_Lean_Elab_expandMacro_x3f(x_2, x_12, x_105, x_98);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_st_ref_take(x_7, x_102);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 6);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 lean_ctor_release(x_110, 6);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 7, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_114);
lean_ctor_set(x_119, 3, x_108);
lean_ctor_set(x_119, 4, x_115);
lean_ctor_set(x_119, 5, x_116);
lean_ctor_set(x_119, 6, x_117);
x_120 = lean_st_ref_set(x_7, x_119, x_111);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_array_push(x_86, x_12);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_87);
x_4 = x_14;
x_5 = x_123;
x_8 = x_121;
goto _start;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_87);
lean_dec(x_12);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_ctor_get(x_107, 0);
lean_inc(x_126);
lean_dec(x_107);
x_127 = lean_array_push(x_86, x_126);
x_128 = 1;
x_129 = lean_box(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_4 = x_14;
x_5 = x_130;
x_8 = x_125;
goto _start;
}
}
else
{
lean_object* x_132; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_14);
lean_dec(x_12);
x_132 = lean_ctor_get(x_106, 0);
lean_inc(x_132);
lean_dec(x_106);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_133, x_136, x_6, x_7, x_102);
lean_dec(x_133);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_6);
x_142 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___rarg(x_102);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_empty___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___closed__1;
x_14 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__2(x_1, x_8, x_11, x_12, x_13, x_2, x_3, x_7);
lean_dec(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l_Lean_nullKind;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Syntax_setArg(x_1, x_9, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = l_Lean_nullKind;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Syntax_setArg(x_1, x_9, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("conflicting namespaces in mutual declaration, using namespace '");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', but used '");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' in previous declaration");
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_21; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_15 = x_4;
} else {
 lean_dec_ref(x_4);
 x_15 = lean_box(0);
}
lean_inc(x_10);
x_21 = l_Lean_Elab_Command_expandDeclNamespace_x3f(x_10);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_16 = x_22;
goto block_20;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_10);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_ctor_set(x_21, 0, x_26);
x_28 = lean_array_push(x_14, x_27);
lean_ctor_set(x_24, 1, x_28);
lean_ctor_set(x_24, 0, x_21);
x_3 = x_12;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_30);
x_32 = lean_array_push(x_14, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
x_3 = x_12;
x_4 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_array_push(x_14, x_37);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_3 = x_12;
x_4 = x_41;
goto _start;
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_16 = x_43;
goto block_20;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_10);
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
x_49 = lean_name_eq(x_45, x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_free_object(x_44);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_50 = l_System_FilePath_dirName___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_47);
x_52 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_Name_toStringWithSep___main(x_50, x_45);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lean_Macro_throwError___rarg(x_48, x_59, x_5, x_6);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_47);
lean_dec(x_45);
x_65 = lean_array_push(x_14, x_48);
lean_ctor_set(x_44, 1, x_65);
lean_ctor_set(x_44, 0, x_13);
x_3 = x_12;
x_4 = x_44;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_44, 0);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_44);
x_69 = lean_name_eq(x_45, x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_70 = l_System_FilePath_dirName___closed__1;
x_71 = l_Lean_Name_toStringWithSep___main(x_70, x_67);
x_72 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2;
x_75 = lean_string_append(x_73, x_74);
x_76 = l_Lean_Name_toStringWithSep___main(x_70, x_45);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_Lean_Macro_throwError___rarg(x_68, x_79, x_5, x_6);
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
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_67);
lean_dec(x_45);
x_85 = lean_array_push(x_14, x_68);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_13);
lean_ctor_set(x_86, 1, x_85);
x_3 = x_12;
x_4 = x_86;
goto _start;
}
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
x_17 = lean_array_push(x_14, x_10);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_3 = x_12;
x_4 = x_18;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___closed__1;
x_10 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1(x_1, x_6, x_8, x_9, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = l_Lean_mkIdentFrom(x_1, x_21);
x_23 = l_Lean_nullKind;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = l_Lean_Syntax_setArg(x_1, x_4, x_24);
x_26 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_22);
x_27 = lean_array_push(x_26, x_22);
x_28 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_empty___closed__1;
x_31 = lean_array_push(x_30, x_29);
x_32 = lean_array_push(x_31, x_25);
x_33 = lean_array_push(x_30, x_22);
x_34 = l_Lean_nullKind___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_37 = lean_array_push(x_36, x_35);
x_38 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_32, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_12, 0, x_41);
lean_ctor_set(x_10, 0, x_12);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
lean_dec(x_12);
x_43 = l_Lean_mkIdentFrom(x_1, x_42);
x_44 = l_Lean_nullKind;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_19);
x_46 = l_Lean_Syntax_setArg(x_1, x_4, x_45);
x_47 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_43);
x_48 = lean_array_push(x_47, x_43);
x_49 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Array_empty___closed__1;
x_52 = lean_array_push(x_51, x_50);
x_53 = lean_array_push(x_52, x_46);
x_54 = lean_array_push(x_51, x_43);
x_55 = l_Lean_nullKind___closed__2;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_58 = lean_array_push(x_57, x_56);
x_59 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_53, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_10, 0, x_63);
return x_10;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_64 = lean_ctor_get(x_10, 1);
lean_inc(x_64);
lean_dec(x_10);
x_65 = lean_ctor_get(x_11, 1);
lean_inc(x_65);
lean_dec(x_11);
x_66 = lean_ctor_get(x_12, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_67 = x_12;
} else {
 lean_dec_ref(x_12);
 x_67 = lean_box(0);
}
x_68 = l_Lean_mkIdentFrom(x_1, x_66);
x_69 = l_Lean_nullKind;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_71 = l_Lean_Syntax_setArg(x_1, x_4, x_70);
x_72 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_68);
x_73 = lean_array_push(x_72, x_68);
x_74 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Array_empty___closed__1;
x_77 = lean_array_push(x_76, x_75);
x_78 = lean_array_push(x_77, x_71);
x_79 = lean_array_push(x_76, x_68);
x_80 = l_Lean_nullKind___closed__2;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_83 = lean_array_push(x_82, x_81);
x_84 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_array_push(x_78, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_67)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_67;
}
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_64);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_10);
if (x_90 == 0)
{
return x_10;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_10, 0);
x_92 = lean_ctor_get(x_10, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_10);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutual block");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_133 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_4);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_st_ref_get(x_3, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_st_ref_get(x_3, x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 3);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_2, 2);
lean_inc(x_144);
x_145 = lean_st_ref_get(x_3, x_142);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 4);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_environment_main_module(x_139);
x_150 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_134);
lean_ctor_set(x_150, 2, x_144);
lean_ctor_set(x_150, 3, x_148);
lean_inc(x_1);
x_151 = l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f(x_1, x_150, x_143);
lean_dec(x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_take(x_3, x_147);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = !lean_is_exclusive(x_155);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_155, 3);
lean_dec(x_158);
lean_ctor_set(x_155, 3, x_153);
x_159 = lean_st_ref_set(x_3, x_155, x_156);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_5 = x_152;
x_6 = x_160;
goto block_132;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_161 = lean_ctor_get(x_155, 0);
x_162 = lean_ctor_get(x_155, 1);
x_163 = lean_ctor_get(x_155, 2);
x_164 = lean_ctor_get(x_155, 4);
x_165 = lean_ctor_get(x_155, 5);
x_166 = lean_ctor_get(x_155, 6);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_155);
x_167 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_153);
lean_ctor_set(x_167, 4, x_164);
lean_ctor_set(x_167, 5, x_165);
lean_ctor_set(x_167, 6, x_166);
x_168 = lean_st_ref_set(x_3, x_167, x_156);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_5 = x_152;
x_6 = x_169;
goto block_132;
}
block_132:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_3, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_get(x_3, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 3);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_st_ref_get(x_3, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 4);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_environment_main_module(x_48);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_57);
lean_inc(x_1);
x_60 = l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f(x_1, x_59, x_52);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_take(x_3, x_56);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 3);
lean_dec(x_67);
lean_ctor_set(x_64, 3, x_62);
x_68 = lean_st_ref_set(x_3, x_64, x_65);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_10 = x_61;
x_11 = x_69;
goto block_41;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
x_72 = lean_ctor_get(x_64, 2);
x_73 = lean_ctor_get(x_64, 4);
x_74 = lean_ctor_get(x_64, 5);
x_75 = lean_ctor_get(x_64, 6);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_76 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_62);
lean_ctor_set(x_76, 4, x_73);
lean_ctor_set(x_76, 5, x_74);
lean_ctor_set(x_76, 6, x_75);
x_77 = lean_st_ref_set(x_3, x_76, x_65);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_10 = x_61;
x_11 = x_78;
goto block_41;
}
}
else
{
lean_object* x_79; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
lean_dec(x_60);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_80, x_83, x_2, x_3, x_56);
lean_dec(x_3);
lean_dec(x_80);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_3);
lean_dec(x_2);
x_89 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___spec__1___rarg(x_56);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_8, 0);
lean_inc(x_94);
lean_dec(x_8);
x_95 = !lean_is_exclusive(x_2);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_2, 4);
lean_inc(x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_2, 4, x_98);
x_99 = l_Lean_Elab_Command_elabCommand___main(x_94, x_2, x_3, x_9);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_2, 0);
x_101 = lean_ctor_get(x_2, 1);
x_102 = lean_ctor_get(x_2, 2);
x_103 = lean_ctor_get(x_2, 3);
x_104 = lean_ctor_get(x_2, 4);
x_105 = lean_ctor_get(x_2, 5);
x_106 = lean_ctor_get(x_2, 6);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_2);
lean_inc(x_94);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_94);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
x_109 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_108);
lean_ctor_set(x_109, 5, x_105);
lean_ctor_set(x_109, 6, x_106);
x_110 = l_Lean_Elab_Command_elabCommand___main(x_94, x_109, x_3, x_9);
return x_110;
}
}
block_41:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; 
x_12 = l___private_Lean_Elab_Declaration_3__isMutualInductive(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l___private_Lean_Elab_Declaration_5__isMutualDef(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_Lean_Elab_Command_elabMutual___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_14, x_2, x_3, x_11);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Elab_Command_elabMutualDef(x_18, x_2, x_3, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Declaration_4__elabMutualInductive(x_22, x_2, x_3, x_11);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 4);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_2, 4, x_28);
x_29 = l_Lean_Elab_Command_elabCommand___main(x_24, x_2, x_3, x_11);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
x_33 = lean_ctor_get(x_2, 3);
x_34 = lean_ctor_get(x_2, 4);
x_35 = lean_ctor_get(x_2, 5);
x_36 = lean_ctor_get(x_2, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_24);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_36);
x_40 = l_Lean_Elab_Command_elabCommand___main(x_24, x_39, x_3, x_11);
return x_40;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_7);
if (x_111 == 0)
{
return x_7;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_7, 0);
x_113 = lean_ctor_get(x_7, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_7);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_5, 0);
lean_inc(x_115);
lean_dec(x_5);
x_116 = !lean_is_exclusive(x_2);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_2, 4);
lean_inc(x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_115);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_2, 4, x_119);
x_120 = l_Lean_Elab_Command_elabCommand___main(x_115, x_2, x_3, x_6);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
x_123 = lean_ctor_get(x_2, 2);
x_124 = lean_ctor_get(x_2, 3);
x_125 = lean_ctor_get(x_2, 4);
x_126 = lean_ctor_get(x_2, 5);
x_127 = lean_ctor_get(x_2, 6);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_2);
lean_inc(x_115);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_115);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
x_130 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_122);
lean_ctor_set(x_130, 2, x_123);
lean_ctor_set(x_130, 3, x_124);
lean_ctor_set(x_130, 4, x_129);
lean_ctor_set(x_130, 5, x_126);
lean_ctor_set(x_130, 6, x_127);
x_131 = l_Lean_Elab_Command_elabCommand___main(x_115, x_130, x_3, x_6);
return x_131;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mutual");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
lean_object* initialize_Lean_Elab_Definition(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
lean_object* initialize_Lean_Elab_Structure(lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Declaration(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Definition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__1 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__1);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__2);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__3 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__3);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__4);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__5 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__5);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__6);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__7 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__7);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__8);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__9 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__9);
l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10 = _init_l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclNamespace_x3f___closed__10);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6);
l_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__1);
l_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__2);
l_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__3);
l_Lean_Elab_Command_elabDeclaration___closed__4 = _init_l_Lean_Elab_Command_elabDeclaration___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__4);
l_Lean_Elab_Command_elabDeclaration___closed__5 = _init_l_Lean_Elab_Command_elabDeclaration___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__5);
l_Lean_Elab_Command_elabDeclaration___closed__6 = _init_l_Lean_Elab_Command_elabDeclaration___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__6);
l_Lean_Elab_Command_elabDeclaration___closed__7 = _init_l_Lean_Elab_Command_elabDeclaration___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__7);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__1);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__2 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__2);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__3 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__3);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__4 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__4);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__5 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__5);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__6 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__6);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__7);
l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8 = _init_l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_8__expandMutualPreamble_x3f___closed__8);
l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualElement_x3f___closed__1);
l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__1);
l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__2);
l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___spec__1___closed__3);
l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_10__expandMutualNamespace_x3f___closed__1);
l_Lean_Elab_Command_elabMutual___closed__1 = _init_l_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__1);
l_Lean_Elab_Command_elabMutual___closed__2 = _init_l_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__2);
l_Lean_Elab_Command_elabMutual___closed__3 = _init_l_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabMutual(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
