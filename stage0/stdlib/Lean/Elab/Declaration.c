// Lean compiler output
// Module: Lean.Elab.Declaration
// Imports: Init Lean.Util.CollectLevelParams Lean.Elab.DeclUtil Lean.Elab.DefView Lean.Elab.Inductive Lean.Elab.Structure Lean.Elab.MutualDef Lean.Elab.DeclarationRange
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
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_getTerminationHints___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4;
lean_object* l_Lean_extractMacroScopes(lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__9;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__8;
lean_object* l_Lean_Elab_Command_elabMutualDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__7;
uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__5;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2;
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__5;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39;
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__2;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_mkDefViewOfInstance___spec__11(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1;
lean_object* l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__1;
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__3;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__7;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getTerminationHints(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__25;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__27;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4;
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36;
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__4;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__6___boxed(lean_object**);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_classInductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__2;
extern lean_object* l_Lean_LocalContext_empty;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__5;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11;
static lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__6;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__19;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandMutualNamespace___closed__1;
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__6;
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__6;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__6;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getTerminationHints___boxed(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__16;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__1;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabMutual___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__10;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__2;
static lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_expandMutualElement___closed__1;
static lean_object* l_Lean_Elab_Command_expandMutualPreamble___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr___closed__1;
uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
static lean_object* l_Lean_Elab_Command_expandMutualPreamble___closed__3;
static lean_object* l_Lean_Elab_Command_elabClassInductive___closed__3;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___boxed(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMutual___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__3;
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__30;
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabMutualDef_processDeriving___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAttr___closed__1;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__4;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__21;
static lean_object* l_Lean_Elab_Command_elabClassInductive___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__9;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualElement(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabClassInductive___closed__1;
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandMutualPreamble___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__6;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__1;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__10;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15;
extern lean_object* l_Lean_Elab_macroAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5;
lean_object* l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_Command_elabCommand___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInductive___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_object* l_Lean_Elab_Term_applyAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__24;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__2;
static lean_object* l_Lean_Elab_Command_getTerminationHints___closed__5;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabDeclaration___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__37;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMutual___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11;
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17;
static lean_object* l_Lean_Elab_Command_elabMutual___lambda__2___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Command_getTerminationHints___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_7661_(lean_object*);
static lean_object* l_Lean_Elab_Command_getTerminationHints___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4;
lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(size_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMutual___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__3;
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__21;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5;
static size_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__6;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__3;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__7;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1;
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34;
lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__5;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__13;
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__9;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__5;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__4;
lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__3;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__5;
lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__9;
static lean_object* l_Lean_Elab_Command_getTerminationHints___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMutual___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_root_", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid namespace '", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', '_root_' is a reserved namespace", 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', it must not contain numeric parts", 36);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_11 = 1;
x_12 = l_Lean_Name_toString(x_1, x_11);
x_13 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_Macro_throwError___rarg(x_16, x_2, x_3);
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
default: 
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = 1;
x_23 = l_Lean_Name_toString(x_1, x_22);
x_24 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_Macro_throwError___rarg(x_27, x_2, x_3);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_extractMacroScopes(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_8);
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_8, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = l_Lean_Name_str___override(x_15, x_11);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Lean_MacroScopesView_review(x_20);
x_22 = l_Lean_Syntax_getHeadInfo(x_2);
x_23 = lean_mk_syntax_ident(x_21);
x_24 = l_Lean_Syntax_setInfo(x_22, x_23);
x_25 = l_Lean_Syntax_isIdent(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_setArg(x_2, x_26, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_12, 0, x_29);
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_24);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_box(0);
x_34 = l_Lean_Name_str___override(x_33, x_11);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 3);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Lean_MacroScopesView_review(x_38);
x_40 = l_Lean_Syntax_getHeadInfo(x_2);
x_41 = lean_mk_syntax_ident(x_39);
x_42 = l_Lean_Syntax_setInfo(x_40, x_41);
x_43 = l_Lean_Syntax_isIdent(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_Syntax_setArg(x_2, x_44, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_32);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_42);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_5);
return x_57;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Elab_expandDeclIdCore(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___closed__1;
x_7 = l_Lean_Name_isPrefixOf(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___lambda__1(x_5, x_1, x_8, x_2, x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Name_replacePrefix(x_5, x_6, x_10);
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_11, x_2, x_3);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("abbrev", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("theorem", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("opaque", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("axiom", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inductive", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("classInductive", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structure", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instance", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__25;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_inc(x_9);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__10;
x_12 = lean_name_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12;
x_14 = lean_name_eq(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14;
x_16 = lean_name_eq(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__16;
x_18 = lean_name_eq(x_10, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18;
x_20 = lean_name_eq(x_10, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20;
x_22 = lean_name_eq(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22;
x_24 = lean_name_eq(x_10, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24;
x_26 = lean_name_eq(x_10, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26;
x_28 = lean_name_eq(x_10, x_27);
lean_dec(x_10);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(3u);
x_32 = l_Lean_Syntax_getArg(x_9, x_31);
x_33 = l_Lean_Syntax_isNone(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_32, x_34);
x_36 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_35, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_36, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_46, 1);
x_50 = l_Lean_Syntax_setArg(x_32, x_34, x_49);
x_51 = l_Lean_Syntax_setArg(x_9, x_31, x_50);
x_52 = l_Lean_Syntax_setArg(x_1, x_8, x_51);
lean_ctor_set(x_46, 1, x_52);
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
x_55 = l_Lean_Syntax_setArg(x_32, x_34, x_54);
x_56 = l_Lean_Syntax_setArg(x_9, x_31, x_55);
x_57 = l_Lean_Syntax_setArg(x_1, x_8, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_37, 0, x_58);
return x_36;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_37, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_dec(x_36);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Syntax_setArg(x_32, x_34, x_62);
x_65 = l_Lean_Syntax_setArg(x_9, x_31, x_64);
x_66 = l_Lean_Syntax_setArg(x_1, x_8, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_37, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_37);
lean_ctor_set(x_68, 1, x_60);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_37, 0);
lean_inc(x_69);
lean_dec(x_37);
x_70 = lean_ctor_get(x_36, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_71 = x_36;
} else {
 lean_dec_ref(x_36);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
x_75 = l_Lean_Syntax_setArg(x_32, x_34, x_73);
x_76 = l_Lean_Syntax_setArg(x_9, x_31, x_75);
x_77 = l_Lean_Syntax_setArg(x_1, x_8, x_76);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
if (lean_is_scalar(x_71)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_71;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_36);
if (x_81 == 0)
{
return x_36;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_36, 0);
x_83 = lean_ctor_get(x_36, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_36);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_10);
x_87 = l_Lean_Syntax_getArg(x_9, x_8);
x_88 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_87, x_2, x_3);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_9);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set(x_88, 0, x_92);
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_89);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_88);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_88, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 1);
x_102 = l_Lean_Syntax_setArg(x_9, x_8, x_101);
x_103 = l_Lean_Syntax_setArg(x_1, x_8, x_102);
lean_ctor_set(x_98, 1, x_103);
return x_88;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = l_Lean_Syntax_setArg(x_9, x_8, x_105);
x_107 = l_Lean_Syntax_setArg(x_1, x_8, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_89, 0, x_108);
return x_88;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_89, 0);
x_110 = lean_ctor_get(x_88, 1);
lean_inc(x_110);
lean_dec(x_88);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_113 = x_109;
} else {
 lean_dec_ref(x_109);
 x_113 = lean_box(0);
}
x_114 = l_Lean_Syntax_setArg(x_9, x_8, x_112);
x_115 = l_Lean_Syntax_setArg(x_1, x_8, x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_89, 0, x_116);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_89);
lean_ctor_set(x_117, 1, x_110);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_118 = lean_ctor_get(x_89, 0);
lean_inc(x_118);
lean_dec(x_89);
x_119 = lean_ctor_get(x_88, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_120 = x_88;
} else {
 lean_dec_ref(x_88);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
x_124 = l_Lean_Syntax_setArg(x_9, x_8, x_122);
x_125 = l_Lean_Syntax_setArg(x_1, x_8, x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
if (lean_is_scalar(x_120)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_120;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_119);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_9);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_88);
if (x_129 == 0)
{
return x_88;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_88, 0);
x_131 = lean_ctor_get(x_88, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_88);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_10);
x_133 = l_Lean_Syntax_getArg(x_9, x_8);
x_134 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_133, x_2, x_3);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
lean_dec(x_9);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
x_138 = lean_box(0);
lean_ctor_set(x_134, 0, x_138);
return x_134;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_135);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_134);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_ctor_get(x_134, 0);
lean_dec(x_145);
x_146 = !lean_is_exclusive(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_144, 1);
x_148 = l_Lean_Syntax_setArg(x_9, x_8, x_147);
x_149 = l_Lean_Syntax_setArg(x_1, x_8, x_148);
lean_ctor_set(x_144, 1, x_149);
return x_134;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_144, 0);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_144);
x_152 = l_Lean_Syntax_setArg(x_9, x_8, x_151);
x_153 = l_Lean_Syntax_setArg(x_1, x_8, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_135, 0, x_154);
return x_134;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_135, 0);
x_156 = lean_ctor_get(x_134, 1);
lean_inc(x_156);
lean_dec(x_134);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = l_Lean_Syntax_setArg(x_9, x_8, x_158);
x_161 = l_Lean_Syntax_setArg(x_1, x_8, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_135, 0, x_162);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_135);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_164 = lean_ctor_get(x_135, 0);
lean_inc(x_164);
lean_dec(x_135);
x_165 = lean_ctor_get(x_134, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_166 = x_134;
} else {
 lean_dec_ref(x_134);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_170 = l_Lean_Syntax_setArg(x_9, x_8, x_168);
x_171 = l_Lean_Syntax_setArg(x_1, x_8, x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
if (lean_is_scalar(x_166)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_166;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_165);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_9);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_134);
if (x_175 == 0)
{
return x_134;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_134, 0);
x_177 = lean_ctor_get(x_134, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_134);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_10);
x_179 = l_Lean_Syntax_getArg(x_9, x_8);
x_180 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_179, x_2, x_3);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
lean_dec(x_9);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_180);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_180, 0);
lean_dec(x_183);
x_184 = lean_box(0);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
lean_dec(x_180);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_181);
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_180);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = lean_ctor_get(x_181, 0);
x_191 = lean_ctor_get(x_180, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_190, 1);
x_194 = l_Lean_Syntax_setArg(x_9, x_8, x_193);
x_195 = l_Lean_Syntax_setArg(x_1, x_8, x_194);
lean_ctor_set(x_190, 1, x_195);
return x_180;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_190, 0);
x_197 = lean_ctor_get(x_190, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_190);
x_198 = l_Lean_Syntax_setArg(x_9, x_8, x_197);
x_199 = l_Lean_Syntax_setArg(x_1, x_8, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_181, 0, x_200);
return x_180;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_181, 0);
x_202 = lean_ctor_get(x_180, 1);
lean_inc(x_202);
lean_dec(x_180);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
x_206 = l_Lean_Syntax_setArg(x_9, x_8, x_204);
x_207 = l_Lean_Syntax_setArg(x_1, x_8, x_206);
if (lean_is_scalar(x_205)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_205;
}
lean_ctor_set(x_208, 0, x_203);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_181, 0, x_208);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_181);
lean_ctor_set(x_209, 1, x_202);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_181, 0);
lean_inc(x_210);
lean_dec(x_181);
x_211 = lean_ctor_get(x_180, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_212 = x_180;
} else {
 lean_dec_ref(x_180);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_215 = x_210;
} else {
 lean_dec_ref(x_210);
 x_215 = lean_box(0);
}
x_216 = l_Lean_Syntax_setArg(x_9, x_8, x_214);
x_217 = l_Lean_Syntax_setArg(x_1, x_8, x_216);
if (lean_is_scalar(x_215)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_215;
}
lean_ctor_set(x_218, 0, x_213);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
if (lean_is_scalar(x_212)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_212;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_211);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_9);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_180);
if (x_221 == 0)
{
return x_180;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_180, 0);
x_223 = lean_ctor_get(x_180, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_180);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_10);
x_225 = l_Lean_Syntax_getArg(x_9, x_8);
x_226 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_225, x_2, x_3);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_228; 
lean_dec(x_9);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_226);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_226, 0);
lean_dec(x_229);
x_230 = lean_box(0);
lean_ctor_set(x_226, 0, x_230);
return x_226;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
lean_dec(x_226);
x_232 = lean_box(0);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_227);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_226);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_227, 0);
x_237 = lean_ctor_get(x_226, 0);
lean_dec(x_237);
x_238 = !lean_is_exclusive(x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_236, 1);
x_240 = l_Lean_Syntax_setArg(x_9, x_8, x_239);
x_241 = l_Lean_Syntax_setArg(x_1, x_8, x_240);
lean_ctor_set(x_236, 1, x_241);
return x_226;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_236, 0);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_236);
x_244 = l_Lean_Syntax_setArg(x_9, x_8, x_243);
x_245 = l_Lean_Syntax_setArg(x_1, x_8, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_227, 0, x_246);
return x_226;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_247 = lean_ctor_get(x_227, 0);
x_248 = lean_ctor_get(x_226, 1);
lean_inc(x_248);
lean_dec(x_226);
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_251 = x_247;
} else {
 lean_dec_ref(x_247);
 x_251 = lean_box(0);
}
x_252 = l_Lean_Syntax_setArg(x_9, x_8, x_250);
x_253 = l_Lean_Syntax_setArg(x_1, x_8, x_252);
if (lean_is_scalar(x_251)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_251;
}
lean_ctor_set(x_254, 0, x_249);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set(x_227, 0, x_254);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_227);
lean_ctor_set(x_255, 1, x_248);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_256 = lean_ctor_get(x_227, 0);
lean_inc(x_256);
lean_dec(x_227);
x_257 = lean_ctor_get(x_226, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_258 = x_226;
} else {
 lean_dec_ref(x_226);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_261 = x_256;
} else {
 lean_dec_ref(x_256);
 x_261 = lean_box(0);
}
x_262 = l_Lean_Syntax_setArg(x_9, x_8, x_260);
x_263 = l_Lean_Syntax_setArg(x_1, x_8, x_262);
if (lean_is_scalar(x_261)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_261;
}
lean_ctor_set(x_264, 0, x_259);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
if (lean_is_scalar(x_258)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_258;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_257);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_9);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_226);
if (x_267 == 0)
{
return x_226;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_226, 0);
x_269 = lean_ctor_get(x_226, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_226);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_10);
x_271 = l_Lean_Syntax_getArg(x_9, x_8);
x_272 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_271, x_2, x_3);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
lean_dec(x_9);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_272);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_272, 0);
lean_dec(x_275);
x_276 = lean_box(0);
lean_ctor_set(x_272, 0, x_276);
return x_272;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
lean_dec(x_272);
x_278 = lean_box(0);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_273);
if (x_280 == 0)
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_272);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_273, 0);
x_283 = lean_ctor_get(x_272, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_282, 1);
x_286 = l_Lean_Syntax_setArg(x_9, x_8, x_285);
x_287 = l_Lean_Syntax_setArg(x_1, x_8, x_286);
lean_ctor_set(x_282, 1, x_287);
return x_272;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_288 = lean_ctor_get(x_282, 0);
x_289 = lean_ctor_get(x_282, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_282);
x_290 = l_Lean_Syntax_setArg(x_9, x_8, x_289);
x_291 = l_Lean_Syntax_setArg(x_1, x_8, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_291);
lean_ctor_set(x_273, 0, x_292);
return x_272;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_293 = lean_ctor_get(x_273, 0);
x_294 = lean_ctor_get(x_272, 1);
lean_inc(x_294);
lean_dec(x_272);
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_297 = x_293;
} else {
 lean_dec_ref(x_293);
 x_297 = lean_box(0);
}
x_298 = l_Lean_Syntax_setArg(x_9, x_8, x_296);
x_299 = l_Lean_Syntax_setArg(x_1, x_8, x_298);
if (lean_is_scalar(x_297)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_297;
}
lean_ctor_set(x_300, 0, x_295);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_273, 0, x_300);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_273);
lean_ctor_set(x_301, 1, x_294);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_302 = lean_ctor_get(x_273, 0);
lean_inc(x_302);
lean_dec(x_273);
x_303 = lean_ctor_get(x_272, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_304 = x_272;
} else {
 lean_dec_ref(x_272);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_302, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_302, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_307 = x_302;
} else {
 lean_dec_ref(x_302);
 x_307 = lean_box(0);
}
x_308 = l_Lean_Syntax_setArg(x_9, x_8, x_306);
x_309 = l_Lean_Syntax_setArg(x_1, x_8, x_308);
if (lean_is_scalar(x_307)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_307;
}
lean_ctor_set(x_310, 0, x_305);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
if (lean_is_scalar(x_304)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_304;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_303);
return x_312;
}
}
}
else
{
uint8_t x_313; 
lean_dec(x_9);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_272);
if (x_313 == 0)
{
return x_272;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_272, 0);
x_315 = lean_ctor_get(x_272, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_272);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_10);
x_317 = l_Lean_Syntax_getArg(x_9, x_8);
x_318 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_317, x_2, x_3);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; 
lean_dec(x_9);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_318);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_318, 0);
lean_dec(x_321);
x_322 = lean_box(0);
lean_ctor_set(x_318, 0, x_322);
return x_318;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_dec(x_318);
x_324 = lean_box(0);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
uint8_t x_326; 
x_326 = !lean_is_exclusive(x_319);
if (x_326 == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_318);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_328 = lean_ctor_get(x_319, 0);
x_329 = lean_ctor_get(x_318, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_328);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_328, 1);
x_332 = l_Lean_Syntax_setArg(x_9, x_8, x_331);
x_333 = l_Lean_Syntax_setArg(x_1, x_8, x_332);
lean_ctor_set(x_328, 1, x_333);
return x_318;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_334 = lean_ctor_get(x_328, 0);
x_335 = lean_ctor_get(x_328, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_328);
x_336 = l_Lean_Syntax_setArg(x_9, x_8, x_335);
x_337 = l_Lean_Syntax_setArg(x_1, x_8, x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_334);
lean_ctor_set(x_338, 1, x_337);
lean_ctor_set(x_319, 0, x_338);
return x_318;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_339 = lean_ctor_get(x_319, 0);
x_340 = lean_ctor_get(x_318, 1);
lean_inc(x_340);
lean_dec(x_318);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_343 = x_339;
} else {
 lean_dec_ref(x_339);
 x_343 = lean_box(0);
}
x_344 = l_Lean_Syntax_setArg(x_9, x_8, x_342);
x_345 = l_Lean_Syntax_setArg(x_1, x_8, x_344);
if (lean_is_scalar(x_343)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_343;
}
lean_ctor_set(x_346, 0, x_341);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set(x_319, 0, x_346);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_319);
lean_ctor_set(x_347, 1, x_340);
return x_347;
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_348 = lean_ctor_get(x_319, 0);
lean_inc(x_348);
lean_dec(x_319);
x_349 = lean_ctor_get(x_318, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_350 = x_318;
} else {
 lean_dec_ref(x_318);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_348, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_353 = x_348;
} else {
 lean_dec_ref(x_348);
 x_353 = lean_box(0);
}
x_354 = l_Lean_Syntax_setArg(x_9, x_8, x_352);
x_355 = l_Lean_Syntax_setArg(x_1, x_8, x_354);
if (lean_is_scalar(x_353)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_353;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_356);
if (lean_is_scalar(x_350)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_350;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_349);
return x_358;
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_9);
lean_dec(x_1);
x_359 = !lean_is_exclusive(x_318);
if (x_359 == 0)
{
return x_318;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_318, 0);
x_361 = lean_ctor_get(x_318, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_318);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_10);
x_363 = l_Lean_Syntax_getArg(x_9, x_8);
x_364 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_363, x_2, x_3);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
if (lean_obj_tag(x_365) == 0)
{
uint8_t x_366; 
lean_dec(x_9);
lean_dec(x_1);
x_366 = !lean_is_exclusive(x_364);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_364, 0);
lean_dec(x_367);
x_368 = lean_box(0);
lean_ctor_set(x_364, 0, x_368);
return x_364;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_364, 1);
lean_inc(x_369);
lean_dec(x_364);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
else
{
uint8_t x_372; 
x_372 = !lean_is_exclusive(x_365);
if (x_372 == 0)
{
uint8_t x_373; 
x_373 = !lean_is_exclusive(x_364);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = lean_ctor_get(x_365, 0);
x_375 = lean_ctor_get(x_364, 0);
lean_dec(x_375);
x_376 = !lean_is_exclusive(x_374);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_374, 1);
x_378 = l_Lean_Syntax_setArg(x_9, x_8, x_377);
x_379 = l_Lean_Syntax_setArg(x_1, x_8, x_378);
lean_ctor_set(x_374, 1, x_379);
return x_364;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_380 = lean_ctor_get(x_374, 0);
x_381 = lean_ctor_get(x_374, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_374);
x_382 = l_Lean_Syntax_setArg(x_9, x_8, x_381);
x_383 = l_Lean_Syntax_setArg(x_1, x_8, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_380);
lean_ctor_set(x_384, 1, x_383);
lean_ctor_set(x_365, 0, x_384);
return x_364;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_385 = lean_ctor_get(x_365, 0);
x_386 = lean_ctor_get(x_364, 1);
lean_inc(x_386);
lean_dec(x_364);
x_387 = lean_ctor_get(x_385, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_389 = x_385;
} else {
 lean_dec_ref(x_385);
 x_389 = lean_box(0);
}
x_390 = l_Lean_Syntax_setArg(x_9, x_8, x_388);
x_391 = l_Lean_Syntax_setArg(x_1, x_8, x_390);
if (lean_is_scalar(x_389)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_389;
}
lean_ctor_set(x_392, 0, x_387);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_365, 0, x_392);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_365);
lean_ctor_set(x_393, 1, x_386);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_394 = lean_ctor_get(x_365, 0);
lean_inc(x_394);
lean_dec(x_365);
x_395 = lean_ctor_get(x_364, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_396 = x_364;
} else {
 lean_dec_ref(x_364);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_399 = x_394;
} else {
 lean_dec_ref(x_394);
 x_399 = lean_box(0);
}
x_400 = l_Lean_Syntax_setArg(x_9, x_8, x_398);
x_401 = l_Lean_Syntax_setArg(x_1, x_8, x_400);
if (lean_is_scalar(x_399)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_399;
}
lean_ctor_set(x_402, 0, x_397);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_402);
if (lean_is_scalar(x_396)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_396;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_395);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_9);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_364);
if (x_405 == 0)
{
return x_364;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_364, 0);
x_407 = lean_ctor_get(x_364, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_364);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
}
else
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_10);
x_409 = l_Lean_Syntax_getArg(x_9, x_8);
x_410 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f(x_409, x_2, x_3);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
if (lean_obj_tag(x_411) == 0)
{
uint8_t x_412; 
lean_dec(x_9);
lean_dec(x_1);
x_412 = !lean_is_exclusive(x_410);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_410, 0);
lean_dec(x_413);
x_414 = lean_box(0);
lean_ctor_set(x_410, 0, x_414);
return x_410;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_410, 1);
lean_inc(x_415);
lean_dec(x_410);
x_416 = lean_box(0);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
uint8_t x_418; 
x_418 = !lean_is_exclusive(x_411);
if (x_418 == 0)
{
uint8_t x_419; 
x_419 = !lean_is_exclusive(x_410);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_420 = lean_ctor_get(x_411, 0);
x_421 = lean_ctor_get(x_410, 0);
lean_dec(x_421);
x_422 = !lean_is_exclusive(x_420);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_420, 1);
x_424 = l_Lean_Syntax_setArg(x_9, x_8, x_423);
x_425 = l_Lean_Syntax_setArg(x_1, x_8, x_424);
lean_ctor_set(x_420, 1, x_425);
return x_410;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_426 = lean_ctor_get(x_420, 0);
x_427 = lean_ctor_get(x_420, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_420);
x_428 = l_Lean_Syntax_setArg(x_9, x_8, x_427);
x_429 = l_Lean_Syntax_setArg(x_1, x_8, x_428);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_426);
lean_ctor_set(x_430, 1, x_429);
lean_ctor_set(x_411, 0, x_430);
return x_410;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_431 = lean_ctor_get(x_411, 0);
x_432 = lean_ctor_get(x_410, 1);
lean_inc(x_432);
lean_dec(x_410);
x_433 = lean_ctor_get(x_431, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_435 = x_431;
} else {
 lean_dec_ref(x_431);
 x_435 = lean_box(0);
}
x_436 = l_Lean_Syntax_setArg(x_9, x_8, x_434);
x_437 = l_Lean_Syntax_setArg(x_1, x_8, x_436);
if (lean_is_scalar(x_435)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_435;
}
lean_ctor_set(x_438, 0, x_433);
lean_ctor_set(x_438, 1, x_437);
lean_ctor_set(x_411, 0, x_438);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_411);
lean_ctor_set(x_439, 1, x_432);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_440 = lean_ctor_get(x_411, 0);
lean_inc(x_440);
lean_dec(x_411);
x_441 = lean_ctor_get(x_410, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_442 = x_410;
} else {
 lean_dec_ref(x_410);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_440, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_445 = x_440;
} else {
 lean_dec_ref(x_440);
 x_445 = lean_box(0);
}
x_446 = l_Lean_Syntax_setArg(x_9, x_8, x_444);
x_447 = l_Lean_Syntax_setArg(x_1, x_8, x_446);
if (lean_is_scalar(x_445)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_445;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_448);
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_441);
return x_450;
}
}
}
else
{
uint8_t x_451; 
lean_dec(x_9);
lean_dec(x_1);
x_451 = !lean_is_exclusive(x_410);
if (x_451 == 0)
{
return x_410;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_410, 0);
x_453 = lean_ctor_get(x_410, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_410);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
x_7 = l_Lean_Syntax_getPos_x3f(x_1, x_6);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_FileMap_toPosition(x_5, x_9);
lean_inc(x_10);
x_11 = l_Lean_FileMap_leanPosToLspPos(x_5, x_10);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_FileMap_toPosition(x_5, x_16);
lean_dec(x_16);
lean_inc(x_17);
x_18 = l_Lean_FileMap_leanPosToLspPos(x_5, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l_Lean_FileMap_toPosition(x_5, x_22);
lean_dec(x_22);
lean_inc(x_23);
x_24 = l_Lean_FileMap_leanPosToLspPos(x_5, x_23);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_FileMap_toPosition(x_5, x_29);
lean_dec(x_29);
lean_inc(x_30);
x_31 = l_Lean_FileMap_leanPosToLspPos(x_5, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_declRangeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1;
x_12 = l_Lean_MapDeclarationExtension_insert___rarg(x_11, x_10, x_1, x_2);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_st_ref_set(x_4, x_7, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
x_27 = lean_ctor_get(x_7, 7);
x_28 = lean_ctor_get(x_7, 8);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_29 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1;
x_30 = l_Lean_MapDeclarationExtension_insert___rarg(x_29, x_20, x_1, x_2);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
lean_ctor_set(x_31, 8, x_28);
x_32 = lean_st_ref_set(x_4, x_31, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("example", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2;
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_9 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_2, x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_getDeclarationSelectionRef(x_2);
x_13 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_12, x_3, x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_16, x_3, x_4, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = 1;
x_16 = l_Lean_Elab_Term_addTermInfo_x27(x_2, x_11, x_13, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Elab_Term_applyAttributesAt(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2), 9, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 0;
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_11, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l_Lean_isExtern(x_26, x_2);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = 1;
x_29 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_4, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_10);
return x_29;
}
else
{
lean_object* x_30; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_4, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_10);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__2;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = 2;
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Elab_Term_elabType(x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_25 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_24, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = 1;
x_32 = l_Lean_Meta_mkForallFVars(x_9, x_28, x_24, x_30, x_31, x_12, x_13, x_14, x_15, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_mkForallFVars(x_4, x_33, x_30, x_30, x_31, x_12, x_13, x_14, x_15, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__1;
x_40 = l_Lean_Elab_Term_levelMVarToParam(x_36, x_38, x_39, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__4;
lean_inc(x_43);
x_45 = l_Lean_CollectLevelParams_main(x_43, x_44);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Elab_sortDeclLevelParams(x_5, x_6, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___spec__1(x_7, x_50, x_10, x_11, x_12, x_13, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_7);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_42);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_54);
lean_inc(x_2);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_54);
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7;
x_78 = lean_st_ref_get(x_15, x_55);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 3);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_61 = x_24;
x_62 = x_82;
goto block_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_60, x_10, x_11, x_12, x_13, x_14, x_15, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_61 = x_87;
x_62 = x_86;
goto block_77;
}
block_77:
{
if (x_61 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
x_63 = lean_box(0);
x_64 = l_Lean_Elab_Command_elabAxiom___lambda__4(x_59, x_2, x_8, x_17, x_63, x_10, x_11, x_12, x_13, x_14, x_15, x_62);
lean_dec(x_17);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_2);
x_65 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_65, 0, x_2);
x_66 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__9;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__11;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_54);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
x_73 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_60, x_72, x_10, x_11, x_12, x_13, x_14, x_15, x_62);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Command_elabAxiom___lambda__4(x_59, x_2, x_8, x_17, x_74, x_10, x_11, x_12, x_13, x_14, x_15, x_75);
lean_dec(x_74);
lean_dec(x_17);
return x_76;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_35);
if (x_88 == 0)
{
return x_35;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_35, 0);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_35);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_32);
if (x_92 == 0)
{
return x_32;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_32, 0);
x_94 = lean_ctor_get(x_32, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_32);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_15);
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
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_25);
if (x_96 == 0)
{
return x_25;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_25, 0);
x_98 = lean_ctor_get(x_25, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_25);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_17);
lean_dec(x_15);
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
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_21);
if (x_100 == 0)
{
return x_21;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_21, 0);
x_102 = lean_ctor_get(x_21, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_21);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_17);
lean_dec(x_15);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_19);
if (x_104 == 0)
{
return x_19;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_19, 0);
x_106 = lean_ctor_get(x_19, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_19);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Syntax_getArgs(x_1);
lean_inc(x_6);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__5), 16, 8);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_4);
lean_closure_set(x_19, 3, x_9);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLevelNames___rarg), 9, 2);
lean_closure_set(x_21, 0, x_6);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_22;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_18, x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_array_get_size(x_10);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_24 = l_Array_toSubarray___rarg(x_10, x_23, x_22);
x_25 = lean_ctor_get(x_1, 6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_array_get_size(x_25);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_25, x_28, x_29, x_26, x_11, x_12, x_13, x_14, x_15, x_16, x_20);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_11, 6);
lean_dec(x_35);
lean_ctor_set(x_11, 6, x_33);
x_36 = l_Lean_Core_resetMessageLog(x_15, x_16, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__6___boxed), 17, 8);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_3);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_5);
lean_closure_set(x_38, 4, x_6);
lean_closure_set(x_38, 5, x_7);
lean_closure_set(x_38, 6, x_8);
lean_closure_set(x_38, 7, x_9);
x_39 = l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1;
x_40 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_10, x_39, x_38, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
x_43 = lean_ctor_get(x_11, 2);
x_44 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
x_45 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 1);
x_46 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 2);
x_47 = lean_ctor_get(x_11, 3);
x_48 = lean_ctor_get(x_11, 4);
x_49 = lean_ctor_get(x_11, 5);
x_50 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 3);
x_51 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 4);
x_52 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 5);
x_53 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 6);
x_54 = lean_ctor_get(x_11, 7);
x_55 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 7);
lean_inc(x_54);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_56 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_42);
lean_ctor_set(x_56, 2, x_43);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_49);
lean_ctor_set(x_56, 6, x_33);
lean_ctor_set(x_56, 7, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*8, x_44);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 1, x_45);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 2, x_46);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 3, x_50);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 4, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 5, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 6, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 7, x_55);
x_57 = l_Lean_Core_resetMessageLog(x_15, x_16, x_32);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__6___boxed), 17, 8);
lean_closure_set(x_59, 0, x_2);
lean_closure_set(x_59, 1, x_3);
lean_closure_set(x_59, 2, x_4);
lean_closure_set(x_59, 3, x_5);
lean_closure_set(x_59, 4, x_6);
lean_closure_set(x_59, 5, x_7);
lean_closure_set(x_59, 6, x_8);
lean_closure_set(x_59, 7, x_9);
x_60 = l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1;
x_61 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_10, x_60, x_59, x_56, x_12, x_13, x_14, x_15, x_16, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_16);
lean_dec(x_15);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_7);
x_16 = l_Lean_Elab_Command_expandDeclId(x_7, x_1, x_3, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
lean_inc(x_2);
lean_inc(x_19);
x_21 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_19, x_2, x_3, x_4, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = l_Lean_Elab_Command_getScope___rarg(x_4, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 5);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__7___boxed), 17, 9);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_1);
lean_closure_set(x_28, 3, x_19);
lean_closure_set(x_28, 4, x_12);
lean_closure_set(x_28, 5, x_14);
lean_closure_set(x_28, 6, x_20);
lean_closure_set(x_28, 7, x_2);
lean_closure_set(x_28, 8, x_7);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_Command_liftTermElabM___rarg(x_23, x_30, x_3, x_4, x_26);
lean_dec(x_4);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabAxiom___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__6___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Command_elabAxiom___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Command_elabAxiom___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_1);
return x_18;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid use of attributes in constructor declaration", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2;
x_11 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid use of 'unsafe' in constructor declaration", 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid use of 'partial' in constructor declaration", 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = l_Lean_Elab_Modifiers_isPartial(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid use of 'noncomputable' in constructor declaration", 57);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(x_1, x_6, x_2, x_3, x_4);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_8, x_2, x_3, x_4);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_3, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_13, x_4, x_5, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getIdAt(x_2, x_10);
x_12 = l_Lean_Name_append(x_3, x_11);
x_13 = l_Lean_Syntax_getArg(x_2, x_10);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = l_Lean_Elab_Command_getRef(x_5, x_6, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_replaceRef(x_13, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 7);
lean_inc(x_25);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_26, 6, x_18);
lean_ctor_set(x_26, 7, x_25);
lean_inc(x_6);
x_27 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(x_14, x_12, x_26, x_6, x_17);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_2, x_30);
x_32 = l_Lean_Elab_expandOptDeclSig(x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_inc(x_28);
x_36 = l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__9(x_28, x_35, x_5, x_6, x_29);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_2);
lean_inc(x_28);
x_38 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(x_28, x_2, x_13, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_1);
lean_ctor_set(x_41, 2, x_28);
lean_ctor_set(x_41, 3, x_33);
lean_ctor_set(x_41, 4, x_34);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_28);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'protected' constructor in a 'private' inductive datatype", 65);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = l_Lean_Elab_Modifiers_isProtected(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(x_1, x_2, x_3, x_10, x_6, x_7, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Elab_Modifiers_isPrivate(x_4);
lean_dec(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(x_1, x_2, x_3, x_13, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2;
x_16 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_15, x_6, x_7, x_8);
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'private' constructor in a 'private' inductive datatype", 63);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_11, x_14);
x_16 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_replaceRef(x_11, x_17);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 7);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set(x_27, 6, x_19);
lean_ctor_set(x_27, 7, x_26);
lean_inc(x_7);
lean_inc(x_27);
x_28 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_15, x_27, x_7, x_18);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Modifiers_isPrivate(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
lean_inc(x_7);
lean_inc(x_1);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(x_29, x_11, x_2, x_1, x_32, x_27, x_7, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_38 = lean_array_uset(x_13, x_4, x_34);
x_4 = x_37;
x_5 = x_38;
x_8 = x_35;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
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
x_44 = l_Lean_Elab_Modifiers_isPrivate(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
lean_inc(x_7);
lean_inc(x_1);
x_46 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(x_29, x_11, x_2, x_1, x_45, x_27, x_7, x_30);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
x_50 = lean_usize_add(x_4, x_49);
x_51 = lean_array_uset(x_13, x_4, x_47);
x_4 = x_50;
x_5 = x_51;
x_8 = x_48;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
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
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_29);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_57 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2;
x_58 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_57, x_27, x_7, x_30);
lean_dec(x_7);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_28);
if (x_63 == 0)
{
return x_28;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_28, 0);
x_65 = lean_ctor_get(x_28, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_28);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = l_Lean_Syntax_getArg(x_9, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
x_15 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_9, x_18);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_19);
x_21 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_11, x_2, x_20);
x_2 = x_24;
x_3 = x_25;
x_6 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_4);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set(x_16, 5, x_6);
lean_ctor_set(x_16, 6, x_7);
lean_ctor_set(x_16, 7, x_8);
lean_ctor_set(x_16, 8, x_9);
lean_ctor_set(x_16, 9, x_10);
lean_ctor_set(x_16, 10, x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Elab_expandOptDeclSig(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_14);
x_15 = l_Lean_Elab_Command_expandDeclId(x_14, x_1, x_3, x_4, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
lean_dec(x_16);
lean_inc(x_2);
lean_inc(x_19);
x_21 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_19, x_2, x_3, x_4, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_4);
lean_inc(x_1);
x_29 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(x_1, x_19, x_27, x_28, x_25, x_3, x_4, x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Syntax_getNumArgs(x_2);
x_33 = lean_unsigned_to_nat(6u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_unsigned_to_nat(5u);
x_36 = l_Lean_Syntax_getArg(x_2, x_35);
x_37 = l_Lean_Syntax_getOptional_x3f(x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2;
x_39 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_40 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(x_38, x_28, x_39, x_3, x_4, x_31);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Syntax_getArg(x_2, x_33);
lean_inc(x_4);
lean_inc(x_3);
x_44 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(x_43, x_3, x_4, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_2, x_14, x_1, x_18, x_19, x_20, x_11, x_12, x_30, x_45, x_41, x_47, x_3, x_4, x_46);
lean_dec(x_4);
lean_dec(x_3);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_41);
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec(x_37);
x_54 = l_Lean_Syntax_getArg(x_53, x_13);
lean_dec(x_53);
x_55 = l_Lean_Syntax_getArgs(x_54);
lean_dec(x_54);
x_56 = lean_array_get_size(x_55);
x_57 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_58 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(x_57, x_28, x_55, x_3, x_4, x_31);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Syntax_getArg(x_2, x_33);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(x_61, x_3, x_4, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_box(0);
x_66 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_2, x_14, x_1, x_18, x_19, x_20, x_11, x_12, x_30, x_63, x_59, x_65, x_3, x_4, x_64);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_59);
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_unsigned_to_nat(5u);
x_72 = l_Lean_Syntax_getArg(x_2, x_71);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_Lean_Elab_getOptDerivingClasses___at_Lean_Elab_Command_elabStructure___spec__2(x_72, x_3, x_4, x_31);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_77 = lean_box(0);
x_78 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_2, x_14, x_1, x_18, x_19, x_20, x_11, x_12, x_30, x_74, x_76, x_77, x_3, x_4, x_75);
lean_dec(x_4);
lean_dec(x_3);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_73);
if (x_79 == 0)
{
return x_73;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_29, 0);
x_85 = lean_ctor_get(x_29, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_29);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_15);
if (x_87 == 0)
{
return x_15;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_15, 0);
x_89 = lean_ctor_get(x_15, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_15);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
return x_6;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_6, 0);
x_93 = lean_ctor_get(x_6, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_6);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_classInductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInductive___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_elabInductive___closed__1;
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_Elab_Command_elabInductiveViews(x_10, x_3, x_4, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("class", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabClassInductive___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_elabClassInductive___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Elab_Command_elabClassInductive___closed__3;
x_7 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabInductive___closed__1;
x_12 = lean_array_push(x_11, x_9);
x_13 = l_Lean_Elab_Command_elabInductiveViews(x_12, x_3, x_4, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l_Lean_Elab_Command_getTerminationHints___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getTerminationHints___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getTerminationHints___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getTerminationHints___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Command_getTerminationHints___closed__1;
x_2 = l_Lean_Elab_Command_getTerminationHints___closed__2;
x_3 = lean_unsigned_to_nat(73u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Elab_Command_getTerminationHints___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_getTerminationHints___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getTerminationHints(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_inc(x_3);
x_31 = l_Lean_Syntax_getKind(x_3);
x_32 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12;
x_33 = lean_name_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14;
x_35 = lean_name_eq(x_31, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26;
x_37 = lean_name_eq(x_31, x_36);
lean_dec(x_31);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_3);
x_38 = l_Lean_Elab_Command_getTerminationHints___closed__5;
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_box(0);
x_4 = x_39;
goto block_30;
}
}
else
{
lean_object* x_40; 
lean_dec(x_31);
x_40 = lean_box(0);
x_4 = x_40;
goto block_30;
}
}
else
{
lean_object* x_41; 
lean_dec(x_31);
x_41 = lean_box(0);
x_4 = x_41;
goto block_30;
}
block_30:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_5 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_nat_dec_lt(x_8, x_6);
x_10 = lean_nat_sub(x_6, x_2);
x_11 = lean_nat_dec_lt(x_10, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_12 = l_Lean_Elab_Command_getTerminationHints___closed__4;
x_13 = l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(x_12);
x_14 = l_Lean_Syntax_getOptional_x3f(x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_5);
x_15 = l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(x_12);
x_16 = l_Lean_Syntax_getOptional_x3f(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget(x_5, x_10);
lean_dec(x_10);
lean_dec(x_5);
x_19 = l_Lean_Syntax_getOptional_x3f(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_fget(x_5, x_8);
lean_dec(x_8);
x_22 = l_Lean_Syntax_getOptional_x3f(x_21);
lean_dec(x_21);
if (x_11 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_5);
x_23 = l_Lean_Elab_Command_getTerminationHints___closed__4;
x_24 = l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(x_23);
x_25 = l_Lean_Syntax_getOptional_x3f(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_array_fget(x_5, x_10);
lean_dec(x_10);
lean_dec(x_5);
x_28 = l_Lean_Syntax_getOptional_x3f(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getTerminationHints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getTerminationHints(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabDeclaration___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_17, 0, x_8);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_8);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_12);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = l_Lean_Elab_Command_getRef(x_2, x_3, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 3);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_environment_main_module(x_8);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_29);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_24);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_apply_2(x_1, x_39, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_st_ref_take(x_3, x_36);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_47, 3);
lean_dec(x_50);
lean_ctor_set(x_47, 3, x_45);
x_51 = lean_st_ref_set(x_3, x_47, x_48);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = l_List_reverse___rarg(x_53);
x_55 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__9(x_54, x_2, x_3, x_52);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_43);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_43);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
x_62 = lean_ctor_get(x_47, 2);
x_63 = lean_ctor_get(x_47, 4);
x_64 = lean_ctor_get(x_47, 5);
x_65 = lean_ctor_get(x_47, 6);
x_66 = lean_ctor_get(x_47, 7);
x_67 = lean_ctor_get(x_47, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_45);
lean_ctor_set(x_68, 4, x_63);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_68, 6, x_65);
lean_ctor_set(x_68, 7, x_66);
lean_ctor_set(x_68, 8, x_67);
x_69 = lean_st_ref_set(x_3, x_68, x_48);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_44, 1);
lean_inc(x_71);
lean_dec(x_44);
x_72 = l_List_reverse___rarg(x_71);
x_73 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__9(x_72, x_2, x_3, x_70);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_43);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_maxRecDepthErrorMessage;
x_81 = lean_string_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_79);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabDeclaration___spec__2(x_78, x_83, x_2, x_3, x_36);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_79);
x_85 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4(x_78, x_2, x_3, x_36);
lean_dec(x_3);
lean_dec(x_2);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_3);
lean_dec(x_2);
x_86 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg(x_36);
return x_86;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected declaration", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namespace", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("end", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20;
x_15 = lean_name_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22;
x_17 = lean_name_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24;
x_19 = lean_name_eq(x_11, x_18);
lean_dec(x_11);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Elab_Command_isDefLike(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = l_Lean_Elab_Command_elabDeclaration___closed__2;
x_22 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_21, x_2, x_3, x_8);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Elab_Command_elabInductive___closed__1;
lean_inc(x_1);
x_24 = lean_array_push(x_23, x_1);
x_25 = l_Lean_Elab_Command_getTerminationHints(x_1);
lean_dec(x_1);
x_26 = l_Lean_Elab_Command_elabMutualDef(x_24, x_25, x_2, x_3, x_8);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_28, x_2, x_3, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Command_elabStructure(x_30, x_10, x_2, x_3, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_38, x_2, x_3, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Command_elabClassInductive(x_40, x_10, x_2, x_3, x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_49 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_48, x_2, x_3, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Elab_Command_elabInductive(x_50, x_10, x_2, x_3, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Syntax_getArg(x_1, x_57);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_59 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_58, x_2, x_3, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Command_elabAxiom(x_60, x_10, x_2, x_3, x_61);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_6, 1);
lean_inc(x_68);
lean_dec(x_6);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
lean_inc(x_1);
x_71 = l_Lean_mkIdentFrom(x_1, x_69);
x_72 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_mkDefViewOfInstance___spec__11(x_2, x_3, x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_74);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_76);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_73);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_82 = lean_array_push(x_81, x_80);
lean_inc(x_71);
x_83 = lean_array_push(x_82, x_71);
x_84 = lean_box(2);
x_85 = l_Lean_Elab_Command_elabDeclaration___closed__6;
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_83);
x_87 = l_Lean_Elab_Command_elabDeclaration___closed__8;
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Elab_Command_elabInductive___closed__1;
x_90 = lean_array_push(x_89, x_71);
x_91 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_84);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_90);
x_93 = lean_array_push(x_81, x_88);
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Lean_Elab_Command_elabDeclaration___closed__9;
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_94);
x_97 = l_Lean_Elab_Command_elabDeclaration___closed__10;
x_98 = lean_array_push(x_97, x_86);
x_99 = lean_array_push(x_98, x_70);
x_100 = lean_array_push(x_99, x_96);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_84);
lean_ctor_set(x_101, 1, x_91);
lean_ctor_set(x_101, 2, x_100);
lean_inc(x_101);
x_102 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_102, 0, x_101);
x_103 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_1, x_101, x_102, x_2, x_3, x_78);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_6);
if (x_104 == 0)
{
return x_6;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_6, 0);
x_106 = lean_ctor_get(x_6, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_6);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabDeclaration___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabDeclaration___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabDeclaration", 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(178u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(202u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__2;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(178u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(178u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__5;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
goto _start;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(x_4, x_11, x_12);
lean_dec(x_4);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = l_Lean_Syntax_getArg(x_9, x_10);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_14, x_17, x_4, x_5, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_11, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_6 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(x_6, x_7, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabInductiveViews(x_9, x_2, x_3, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_isDefLike(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(x_4, x_11, x_12);
lean_dec(x_4);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("variable", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("universe", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("check", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("set_option", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("open", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10;
x_12 = lean_name_eq(x_2, x_11);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = 1;
return x_14;
}
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Array_toSubarray___rarg(x_1, x_8, x_2);
x_11 = l_Array_ofSubarray___rarg(x_10);
x_12 = l_Array_toSubarray___rarg(x_1, x_2, x_3);
x_13 = l_Array_ofSubarray___rarg(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("conflicting namespaces in mutual declaration, using namespace '", 63);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', but used '", 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' in previous declaration", 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_1, x_3);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc(x_16);
x_20 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_16, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_18, x_16);
lean_ctor_set(x_4, 0, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_4);
x_7 = x_24;
x_8 = x_22;
goto block_13;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_28);
x_30 = lean_array_push(x_18, x_29);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_7 = x_31;
x_8 = x_27;
goto block_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_array_push(x_18, x_35);
lean_ctor_set(x_4, 1, x_36);
lean_ctor_set(x_4, 0, x_37);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_4);
x_7 = x_38;
x_8 = x_33;
goto block_13;
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_array_push(x_18, x_16);
lean_ctor_set(x_4, 0, x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_4);
x_7 = x_42;
x_8 = x_40;
goto block_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_16);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_name_eq(x_45, x_46);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_free_object(x_4);
lean_dec(x_19);
lean_dec(x_18);
x_49 = 1;
x_50 = l_Lean_Name_toString(x_46, x_49);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Lean_Name_toString(x_45, x_49);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = l_Lean_Macro_throwErrorAt___rarg(x_47, x_58, x_5, x_44);
lean_dec(x_47);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_46);
lean_dec(x_45);
x_64 = lean_array_push(x_18, x_47);
lean_ctor_set(x_4, 0, x_64);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_4);
x_7 = x_65;
x_8 = x_44;
goto block_13;
}
}
}
}
else
{
uint8_t x_66; 
lean_free_object(x_4);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_20);
if (x_66 == 0)
{
return x_20;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_20, 0);
x_68 = lean_ctor_get(x_20, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_20);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_4, 0);
x_71 = lean_ctor_get(x_4, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_16);
x_72 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_16, x_5, x_6);
if (lean_obj_tag(x_72) == 0)
{
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_push(x_70, x_16);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_7 = x_77;
x_8 = x_74;
goto block_13;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_16);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
lean_dec(x_72);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_array_push(x_70, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_7 = x_86;
x_8 = x_80;
goto block_13;
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
lean_dec(x_72);
x_89 = lean_array_push(x_70, x_16);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_71);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_7 = x_91;
x_8 = x_88;
goto block_13;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_16);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_ctor_get(x_72, 1);
lean_inc(x_93);
lean_dec(x_72);
x_94 = lean_ctor_get(x_71, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_name_eq(x_94, x_95);
if (x_97 == 0)
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_71);
lean_dec(x_70);
x_98 = 1;
x_99 = l_Lean_Name_toString(x_95, x_98);
x_100 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2;
x_103 = lean_string_append(x_101, x_102);
x_104 = l_Lean_Name_toString(x_94, x_98);
x_105 = lean_string_append(x_103, x_104);
lean_dec(x_104);
x_106 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3;
x_107 = lean_string_append(x_105, x_106);
x_108 = l_Lean_Macro_throwErrorAt___rarg(x_96, x_107, x_5, x_93);
lean_dec(x_96);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_95);
lean_dec(x_94);
x_113 = lean_array_push(x_70, x_96);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_71);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_7 = x_115;
x_8 = x_93;
goto block_13;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_5);
x_116 = lean_ctor_get(x_72, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_72, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_118 = x_72;
} else {
 lean_dec_ref(x_72);
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
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_9;
x_6 = x_8;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualNamespace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Lean_Elab_Command_expandMutualNamespace___closed__1;
lean_inc(x_2);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(x_6, x_8, x_9, x_10, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(1);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_inc(x_1);
x_23 = l_Lean_mkIdentFrom(x_1, x_22);
x_24 = lean_box(2);
x_25 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_21);
x_27 = l_Lean_Syntax_setArg(x_1, x_4, x_26);
x_28 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_20);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_30);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_34 = lean_array_push(x_33, x_32);
lean_inc(x_23);
x_35 = lean_array_push(x_34, x_23);
x_36 = l_Lean_Elab_Command_elabDeclaration___closed__6;
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
x_38 = l_Lean_Elab_Command_elabDeclaration___closed__8;
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Command_elabInductive___closed__1;
x_41 = lean_array_push(x_40, x_23);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_push(x_33, x_39);
x_44 = lean_array_push(x_43, x_42);
x_45 = l_Lean_Elab_Command_elabDeclaration___closed__9;
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_44);
x_47 = l_Lean_Elab_Command_elabDeclaration___closed__10;
x_48 = lean_array_push(x_47, x_37);
x_49 = lean_array_push(x_48, x_27);
x_50 = lean_array_push(x_49, x_46);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_24);
lean_ctor_set(x_51, 1, x_25);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_28, 0, x_51);
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = l_Lean_Elab_Command_elabDeclaration___closed__5;
lean_inc(x_52);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_57 = lean_array_push(x_56, x_55);
lean_inc(x_23);
x_58 = lean_array_push(x_57, x_23);
x_59 = l_Lean_Elab_Command_elabDeclaration___closed__6;
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_24);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_58);
x_61 = l_Lean_Elab_Command_elabDeclaration___closed__8;
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Command_elabInductive___closed__1;
x_64 = lean_array_push(x_63, x_23);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_24);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_array_push(x_56, x_62);
x_67 = lean_array_push(x_66, x_65);
x_68 = l_Lean_Elab_Command_elabDeclaration___closed__9;
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_24);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_67);
x_70 = l_Lean_Elab_Command_elabDeclaration___closed__10;
x_71 = lean_array_push(x_70, x_60);
x_72 = lean_array_push(x_71, x_27);
x_73 = lean_array_push(x_72, x_69);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_24);
lean_ctor_set(x_74, 1, x_25);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_53);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
return x_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mutual", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandMutualNamespace", 21);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualNamespace), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(246u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(263u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__2;
x_4 = lean_unsigned_to_nat(34u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(246u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(246u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__5;
x_4 = lean_unsigned_to_nat(25u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc(x_9);
x_13 = l_Lean_Macro_expandMacro_x3f(x_9, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_11, x_9);
lean_ctor_set(x_4, 0, x_16);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_12);
lean_dec(x_9);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_array_push(x_11, x_21);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_22);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_6 = x_20;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_9);
x_34 = l_Lean_Macro_expandMacro_x3f(x_9, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_push(x_32, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = 1;
x_40 = lean_usize_add(x_3, x_39);
x_3 = x_40;
x_4 = x_38;
x_6 = x_36;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_33);
lean_dec(x_9);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_array_push(x_32, x_43);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_3, x_48);
x_3 = x_49;
x_4 = x_47;
x_6 = x_42;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_5);
x_51 = lean_ctor_get(x_34, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_53 = x_34;
} else {
 lean_dec_ref(x_34);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualElement___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualElement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Lean_Elab_Command_expandMutualElement___closed__1;
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(x_6, x_8, x_9, x_10, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_box(1);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_box(2);
x_25 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = l_Lean_Syntax_setArg(x_1, x_4, x_26);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_box(2);
x_31 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = l_Lean_Syntax_setArg(x_1, x_4, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandMutualElement", 19);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualElement), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(266u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(276u);
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__2;
x_4 = lean_unsigned_to_nat(26u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(266u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(266u);
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__5;
x_4 = lean_unsigned_to_nat(23u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualPreamble___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("section", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualPreamble___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualPreamble___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_3 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_expandMutualPreamble___closed__1;
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_box(2);
x_24 = l_Lean_Elab_Command_expandMutualPreamble___closed__2;
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
x_26 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_13);
x_28 = l_Lean_Syntax_setArg(x_1, x_4, x_27);
x_29 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_Elab_Command_elabDeclaration___closed__8;
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_push(x_19, x_33);
x_35 = lean_array_push(x_34, x_21);
x_36 = l_Lean_Elab_Command_elabDeclaration___closed__9;
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
x_38 = l_Lean_Elab_Command_elabInductive___closed__1;
x_39 = lean_array_push(x_38, x_25);
x_40 = l_Array_append___rarg(x_39, x_12);
x_41 = lean_array_push(x_38, x_28);
x_42 = l_Array_append___rarg(x_40, x_41);
x_43 = lean_array_push(x_38, x_37);
x_44 = l_Array_append___rarg(x_42, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_29, 0, x_45);
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = l_Lean_Elab_Command_elabDeclaration___closed__8;
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_19, x_49);
x_51 = lean_array_push(x_50, x_21);
x_52 = l_Lean_Elab_Command_elabDeclaration___closed__9;
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_51);
x_54 = l_Lean_Elab_Command_elabInductive___closed__1;
x_55 = lean_array_push(x_54, x_25);
x_56 = l_Array_append___rarg(x_55, x_12);
x_57 = lean_array_push(x_54, x_28);
x_58 = l_Array_append___rarg(x_56, x_57);
x_59 = lean_array_push(x_54, x_53);
x_60 = l_Array_append___rarg(x_58, x_59);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_23);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
return x_62;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandMutualPreamble", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualPreamble), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(279u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(286u);
x_2 = lean_unsigned_to_nat(74u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__2;
x_4 = lean_unsigned_to_nat(74u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(279u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(279u);
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__5;
x_4 = lean_unsigned_to_nat(24u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'decreasing_by' in 'mutual' block, it must be used after the 'end' keyword", 82);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__3;
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__14(x_9, x_10, x_3, x_4, x_5);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'termination_by' in 'mutual' block, it must be used after the 'end' keyword", 83);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
x_11 = l_Lean_Elab_Command_getTerminationHints(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
lean_inc(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1(x_11, x_13, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
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
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_11);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__2;
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__14(x_25, x_26, x_5, x_6, x_7);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive(x_8, x_3, x_4, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'decreasing_by' in mutually inductive datatype declaration", 66);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_elabMutual___lambda__1(x_1, x_7, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Elab_Command_elabMutual___lambda__2___closed__2;
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__14(x_9, x_10, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid mutual block", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'termination_by' in mutually inductive datatype declaration", 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getOptional_x3f(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_getOptional_x3f(x_9);
lean_dec(x_9);
lean_inc(x_10);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
x_13 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = l_Lean_Elab_Command_elabMutual___closed__2;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_14, x_2, x_3, x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_2);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1(x_18, x_20, x_21, x_22, x_2, x_3, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Command_elabMutualDef(x_18, x_11, x_2, x_3, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Command_elabMutual___lambda__2(x_1, x_10, x_30, x_2, x_3, x_4);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_7, 0);
lean_inc(x_32);
lean_dec(x_7);
x_33 = l_Lean_Elab_Command_elabMutual___closed__4;
x_34 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__14(x_32, x_33, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabMutual___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabMutual___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabMutual(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabMutual", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(289u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(306u);
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__2;
x_4 = lean_unsigned_to_nat(37u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(289u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(289u);
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__5;
x_4 = lean_unsigned_to_nat(14u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eraseAttr", 9);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown attribute [{attrName}]", 30);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_14 = l_Lean_Syntax_getKind(x_10);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2;
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_array_push(x_12, x_10);
lean_ctor_set(x_4, 0, x_17);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_10, x_21);
x_23 = l_Lean_Syntax_getId(x_22);
lean_dec(x_22);
x_24 = lean_erase_macro_scopes(x_23);
x_25 = lean_st_ref_get(x_6, x_7);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_24);
x_29 = l_Lean_isAttribute(x_28, x_24);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_24);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
x_31 = 2;
x_32 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_30, x_31, x_5, x_6, x_27);
lean_dec(x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
x_7 = x_33;
goto _start;
}
else
{
lean_object* x_37; size_t x_38; size_t x_39; 
lean_dec(x_10);
x_37 = lean_array_push(x_13, x_24);
lean_ctor_set(x_4, 1, x_37);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
x_7 = x_27;
goto _start;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
lean_inc(x_10);
x_43 = l_Lean_Syntax_getKind(x_10);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2;
x_45 = lean_name_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
x_46 = lean_array_push(x_41, x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = 1;
x_49 = lean_usize_add(x_3, x_48);
x_3 = x_49;
x_4 = x_47;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = l_Lean_Syntax_getArg(x_10, x_51);
x_53 = l_Lean_Syntax_getId(x_52);
lean_dec(x_52);
x_54 = lean_erase_macro_scopes(x_53);
x_55 = lean_st_ref_get(x_6, x_7);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_54);
x_59 = l_Lean_isAttribute(x_58, x_54);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; 
lean_dec(x_54);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
x_61 = 2;
x_62 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_60, x_61, x_5, x_6, x_57);
lean_dec(x_10);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_41);
lean_ctor_set(x_64, 1, x_42);
x_65 = 1;
x_66 = lean_usize_add(x_3, x_65);
x_3 = x_66;
x_4 = x_64;
x_7 = x_63;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; 
lean_dec(x_10);
x_68 = lean_array_push(x_42, x_54);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_68);
x_70 = 1;
x_71 = lean_usize_add(x_3, x_70);
x_3 = x_71;
x_4 = x_69;
x_7 = x_57;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_10 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabMutualDef_processDeriving___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 6);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_11);
x_22 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
x_27 = l_Lean_LocalContext_empty;
x_28 = 0;
x_29 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_2);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_11);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_16 = l_Lean_Attribute_erase(x_1, x_15, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_box(0);
x_4 = x_19;
x_5 = x_20;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_Elab_Term_applyAttributes(x_14, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_get_size(x_4);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__3(x_14, x_4, x_19, x_5, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_6, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
x_13 = lean_array_uget(x_4, x_6);
x_14 = lean_box(0);
x_15 = lean_box_usize(x_1);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___lambda__1___boxed), 12, 5);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_15);
x_17 = l_Lean_Elab_Command_getRef(x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_replaceRef(x_13, x_18);
lean_dec(x_18);
lean_dec(x_13);
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 2);
x_24 = lean_ctor_get(x_8, 3);
x_25 = lean_ctor_get(x_8, 4);
x_26 = lean_ctor_get(x_8, 5);
x_27 = lean_ctor_get(x_8, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
lean_ctor_set(x_28, 6, x_20);
lean_ctor_set(x_28, 7, x_27);
x_29 = l_Lean_Elab_Command_liftTermElabM___rarg(x_14, x_16, x_28, x_9, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 1;
x_32 = lean_usize_add(x_6, x_31);
x_33 = lean_box(0);
x_6 = x_32;
x_7 = x_33;
x_10 = x_30;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getSepArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Lean_Elab_Command_elabAttr___closed__1;
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(x_7, x_9, x_10, x_11, x_2, x_3, x_4);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(x_15, x_2, x_3, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(x_10, x_16, x_18, x_22, x_24, x_10, x_25, x_2, x_3, x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAttr___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(x_11, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabAttr(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabAttr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabAttr", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabAttr___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAttr___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabAttr___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(309u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(327u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__2;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(309u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(309u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__4;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__5;
x_4 = lean_unsigned_to_nat(46u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid initialization command, unexpected modifiers", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attributes", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrInstance", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrKind", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabInductive___closed__1;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Attr", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simple", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declId", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__13;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optDeclSig", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeSpec", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__27;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__30;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValSimple", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("do", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_3 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__37;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_matchesNull(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_17 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_16, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_matchesNull(x_19, x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_22 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_21, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Syntax_matchesNull(x_24, x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_27 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_26, x_10, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Syntax_matchesNull(x_29, x_14);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_32 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_31, x_10, x_11);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(5u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = l_Lean_Syntax_matchesNull(x_34, x_14);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_37 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_36, x_10, x_11);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_inc(x_10);
x_38 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_10, x_11);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_10, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
lean_inc(x_2);
x_44 = l_Lean_Name_str___override(x_2, x_43);
x_45 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2;
lean_inc(x_3);
x_46 = l_Lean_Name_str___override(x_3, x_45);
x_47 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3;
lean_inc(x_40);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4;
lean_inc(x_3);
x_50 = l_Lean_Name_str___override(x_3, x_49);
x_51 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5;
lean_inc(x_3);
x_52 = l_Lean_Name_str___override(x_3, x_51);
x_53 = lean_box(2);
x_54 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6;
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7;
x_57 = l_Lean_Name_str___override(x_4, x_56);
x_58 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8;
x_59 = l_Lean_Name_str___override(x_57, x_58);
x_60 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_61 = lean_array_push(x_60, x_5);
x_62 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_63 = lean_array_push(x_61, x_62);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_array_push(x_60, x_55);
x_66 = lean_array_push(x_65, x_64);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_50);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Lean_Elab_Command_elabInductive___closed__1;
x_69 = lean_array_push(x_68, x_67);
x_70 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_53);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
x_72 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9;
lean_inc(x_40);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_40);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Command_elabDeclaration___closed__10;
x_75 = lean_array_push(x_74, x_48);
x_76 = lean_array_push(x_75, x_71);
x_77 = lean_array_push(x_76, x_73);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_53);
lean_ctor_set(x_78, 1, x_46);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_array_push(x_68, x_78);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_53);
lean_ctor_set(x_80, 1, x_70);
lean_ctor_set(x_80, 2, x_79);
x_81 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11;
lean_inc(x_2);
x_82 = l_Lean_Name_str___override(x_2, x_81);
lean_inc(x_40);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_40);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11;
lean_inc(x_2);
x_85 = l_Lean_Name_str___override(x_2, x_84);
x_86 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15;
lean_inc(x_41);
lean_inc(x_42);
x_87 = l_Lean_addMacroScope(x_42, x_86, x_41);
x_88 = lean_box(0);
x_89 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14;
lean_inc(x_40);
x_90 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_90, 0, x_40);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_87);
lean_ctor_set(x_90, 3, x_88);
x_91 = lean_array_push(x_60, x_90);
x_92 = lean_array_push(x_91, x_62);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_53);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16;
lean_inc(x_2);
x_95 = l_Lean_Name_str___override(x_2, x_94);
x_96 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17;
lean_inc(x_3);
x_97 = l_Lean_Name_str___override(x_3, x_96);
x_98 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18;
lean_inc(x_40);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_40);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19;
lean_inc(x_3);
x_101 = l_Lean_Name_str___override(x_3, x_100);
x_102 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23;
lean_inc(x_41);
lean_inc(x_42);
x_103 = l_Lean_addMacroScope(x_42, x_102, x_41);
x_104 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22;
x_105 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25;
lean_inc(x_40);
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_40);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_105);
x_107 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29;
x_108 = l_Lean_addMacroScope(x_42, x_107, x_41);
x_109 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28;
x_110 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31;
lean_inc(x_40);
x_111 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_111, 0, x_40);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_array_push(x_68, x_111);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_53);
lean_ctor_set(x_113, 1, x_70);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_array_push(x_60, x_106);
x_115 = lean_array_push(x_114, x_113);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_53);
lean_ctor_set(x_116, 1, x_101);
lean_ctor_set(x_116, 2, x_115);
x_117 = lean_array_push(x_60, x_99);
x_118 = lean_array_push(x_117, x_116);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_53);
lean_ctor_set(x_119, 1, x_97);
lean_ctor_set(x_119, 2, x_118);
x_120 = lean_array_push(x_68, x_119);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_53);
lean_ctor_set(x_121, 1, x_70);
lean_ctor_set(x_121, 2, x_120);
x_122 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32;
x_123 = lean_array_push(x_122, x_121);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_53);
lean_ctor_set(x_124, 1, x_95);
lean_ctor_set(x_124, 2, x_123);
x_125 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33;
x_126 = l_Lean_Name_str___override(x_2, x_125);
x_127 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34;
lean_inc(x_40);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_40);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35;
x_130 = l_Lean_Name_str___override(x_3, x_129);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_40);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_60, x_131);
x_133 = lean_array_push(x_132, x_6);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_53);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_133);
x_135 = lean_array_push(x_74, x_128);
x_136 = lean_array_push(x_135, x_134);
x_137 = lean_array_push(x_136, x_62);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_53);
lean_ctor_set(x_138, 1, x_126);
lean_ctor_set(x_138, 2, x_137);
x_139 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36;
x_140 = lean_array_push(x_139, x_83);
x_141 = lean_array_push(x_140, x_93);
x_142 = lean_array_push(x_141, x_124);
x_143 = lean_array_push(x_142, x_138);
x_144 = lean_array_push(x_143, x_62);
x_145 = lean_array_push(x_144, x_62);
x_146 = lean_array_push(x_145, x_62);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_53);
lean_ctor_set(x_147, 1, x_82);
lean_ctor_set(x_147, 2, x_146);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39;
x_149 = lean_array_push(x_148, x_80);
x_150 = lean_array_push(x_149, x_62);
x_151 = lean_array_push(x_150, x_62);
x_152 = lean_array_push(x_151, x_62);
x_153 = lean_array_push(x_152, x_62);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_53);
lean_ctor_set(x_154, 1, x_7);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_array_push(x_60, x_154);
x_156 = lean_array_push(x_155, x_147);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_53);
lean_ctor_set(x_157, 1, x_44);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_38, 0, x_157);
return x_38;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_158 = lean_ctor_get(x_9, 0);
lean_inc(x_158);
lean_dec(x_9);
x_159 = lean_array_push(x_68, x_158);
x_160 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_161 = l_Array_append___rarg(x_160, x_159);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_53);
lean_ctor_set(x_162, 1, x_70);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10;
x_164 = lean_array_push(x_163, x_162);
x_165 = lean_array_push(x_164, x_80);
x_166 = lean_array_push(x_165, x_62);
x_167 = lean_array_push(x_166, x_62);
x_168 = lean_array_push(x_167, x_62);
x_169 = lean_array_push(x_168, x_62);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_53);
lean_ctor_set(x_170, 1, x_7);
lean_ctor_set(x_170, 2, x_169);
x_171 = lean_array_push(x_60, x_170);
x_172 = lean_array_push(x_171, x_147);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_53);
lean_ctor_set(x_173, 1, x_44);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_38, 0, x_173);
return x_38;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_174 = lean_ctor_get(x_38, 0);
x_175 = lean_ctor_get(x_38, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_38);
x_176 = lean_ctor_get(x_10, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_10, 1);
lean_inc(x_177);
lean_dec(x_10);
x_178 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
lean_inc(x_2);
x_179 = l_Lean_Name_str___override(x_2, x_178);
x_180 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2;
lean_inc(x_3);
x_181 = l_Lean_Name_str___override(x_3, x_180);
x_182 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3;
lean_inc(x_174);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4;
lean_inc(x_3);
x_185 = l_Lean_Name_str___override(x_3, x_184);
x_186 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5;
lean_inc(x_3);
x_187 = l_Lean_Name_str___override(x_3, x_186);
x_188 = lean_box(2);
x_189 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6;
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_187);
lean_ctor_set(x_190, 2, x_189);
x_191 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7;
x_192 = l_Lean_Name_str___override(x_4, x_191);
x_193 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8;
x_194 = l_Lean_Name_str___override(x_192, x_193);
x_195 = l_Lean_Elab_Command_elabDeclaration___closed__7;
x_196 = lean_array_push(x_195, x_5);
x_197 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_198 = lean_array_push(x_196, x_197);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_194);
lean_ctor_set(x_199, 2, x_198);
x_200 = lean_array_push(x_195, x_190);
x_201 = lean_array_push(x_200, x_199);
x_202 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_202, 0, x_188);
lean_ctor_set(x_202, 1, x_185);
lean_ctor_set(x_202, 2, x_201);
x_203 = l_Lean_Elab_Command_elabInductive___closed__1;
x_204 = lean_array_push(x_203, x_202);
x_205 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_206 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_206, 0, x_188);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_204);
x_207 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9;
lean_inc(x_174);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_174);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_Elab_Command_elabDeclaration___closed__10;
x_210 = lean_array_push(x_209, x_183);
x_211 = lean_array_push(x_210, x_206);
x_212 = lean_array_push(x_211, x_208);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_188);
lean_ctor_set(x_213, 1, x_181);
lean_ctor_set(x_213, 2, x_212);
x_214 = lean_array_push(x_203, x_213);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_188);
lean_ctor_set(x_215, 1, x_205);
lean_ctor_set(x_215, 2, x_214);
x_216 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11;
lean_inc(x_2);
x_217 = l_Lean_Name_str___override(x_2, x_216);
lean_inc(x_174);
x_218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_218, 0, x_174);
lean_ctor_set(x_218, 1, x_216);
x_219 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11;
lean_inc(x_2);
x_220 = l_Lean_Name_str___override(x_2, x_219);
x_221 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15;
lean_inc(x_176);
lean_inc(x_177);
x_222 = l_Lean_addMacroScope(x_177, x_221, x_176);
x_223 = lean_box(0);
x_224 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14;
lean_inc(x_174);
x_225 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_225, 0, x_174);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_222);
lean_ctor_set(x_225, 3, x_223);
x_226 = lean_array_push(x_195, x_225);
x_227 = lean_array_push(x_226, x_197);
x_228 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_228, 0, x_188);
lean_ctor_set(x_228, 1, x_220);
lean_ctor_set(x_228, 2, x_227);
x_229 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16;
lean_inc(x_2);
x_230 = l_Lean_Name_str___override(x_2, x_229);
x_231 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17;
lean_inc(x_3);
x_232 = l_Lean_Name_str___override(x_3, x_231);
x_233 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18;
lean_inc(x_174);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_174);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19;
lean_inc(x_3);
x_236 = l_Lean_Name_str___override(x_3, x_235);
x_237 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23;
lean_inc(x_176);
lean_inc(x_177);
x_238 = l_Lean_addMacroScope(x_177, x_237, x_176);
x_239 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22;
x_240 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25;
lean_inc(x_174);
x_241 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_241, 0, x_174);
lean_ctor_set(x_241, 1, x_239);
lean_ctor_set(x_241, 2, x_238);
lean_ctor_set(x_241, 3, x_240);
x_242 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29;
x_243 = l_Lean_addMacroScope(x_177, x_242, x_176);
x_244 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28;
x_245 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31;
lean_inc(x_174);
x_246 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_246, 0, x_174);
lean_ctor_set(x_246, 1, x_244);
lean_ctor_set(x_246, 2, x_243);
lean_ctor_set(x_246, 3, x_245);
x_247 = lean_array_push(x_203, x_246);
x_248 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_248, 0, x_188);
lean_ctor_set(x_248, 1, x_205);
lean_ctor_set(x_248, 2, x_247);
x_249 = lean_array_push(x_195, x_241);
x_250 = lean_array_push(x_249, x_248);
x_251 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_251, 0, x_188);
lean_ctor_set(x_251, 1, x_236);
lean_ctor_set(x_251, 2, x_250);
x_252 = lean_array_push(x_195, x_234);
x_253 = lean_array_push(x_252, x_251);
x_254 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_254, 0, x_188);
lean_ctor_set(x_254, 1, x_232);
lean_ctor_set(x_254, 2, x_253);
x_255 = lean_array_push(x_203, x_254);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_188);
lean_ctor_set(x_256, 1, x_205);
lean_ctor_set(x_256, 2, x_255);
x_257 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32;
x_258 = lean_array_push(x_257, x_256);
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_188);
lean_ctor_set(x_259, 1, x_230);
lean_ctor_set(x_259, 2, x_258);
x_260 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33;
x_261 = l_Lean_Name_str___override(x_2, x_260);
x_262 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34;
lean_inc(x_174);
x_263 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_263, 0, x_174);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35;
x_265 = l_Lean_Name_str___override(x_3, x_264);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_174);
lean_ctor_set(x_266, 1, x_264);
x_267 = lean_array_push(x_195, x_266);
x_268 = lean_array_push(x_267, x_6);
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_188);
lean_ctor_set(x_269, 1, x_265);
lean_ctor_set(x_269, 2, x_268);
x_270 = lean_array_push(x_209, x_263);
x_271 = lean_array_push(x_270, x_269);
x_272 = lean_array_push(x_271, x_197);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_188);
lean_ctor_set(x_273, 1, x_261);
lean_ctor_set(x_273, 2, x_272);
x_274 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36;
x_275 = lean_array_push(x_274, x_218);
x_276 = lean_array_push(x_275, x_228);
x_277 = lean_array_push(x_276, x_259);
x_278 = lean_array_push(x_277, x_273);
x_279 = lean_array_push(x_278, x_197);
x_280 = lean_array_push(x_279, x_197);
x_281 = lean_array_push(x_280, x_197);
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_188);
lean_ctor_set(x_282, 1, x_217);
lean_ctor_set(x_282, 2, x_281);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39;
x_284 = lean_array_push(x_283, x_215);
x_285 = lean_array_push(x_284, x_197);
x_286 = lean_array_push(x_285, x_197);
x_287 = lean_array_push(x_286, x_197);
x_288 = lean_array_push(x_287, x_197);
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_188);
lean_ctor_set(x_289, 1, x_7);
lean_ctor_set(x_289, 2, x_288);
x_290 = lean_array_push(x_195, x_289);
x_291 = lean_array_push(x_290, x_282);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_188);
lean_ctor_set(x_292, 1, x_179);
lean_ctor_set(x_292, 2, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_175);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_294 = lean_ctor_get(x_9, 0);
lean_inc(x_294);
lean_dec(x_9);
x_295 = lean_array_push(x_203, x_294);
x_296 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_297 = l_Array_append___rarg(x_296, x_295);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_188);
lean_ctor_set(x_298, 1, x_205);
lean_ctor_set(x_298, 2, x_297);
x_299 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10;
x_300 = lean_array_push(x_299, x_298);
x_301 = lean_array_push(x_300, x_215);
x_302 = lean_array_push(x_301, x_197);
x_303 = lean_array_push(x_302, x_197);
x_304 = lean_array_push(x_303, x_197);
x_305 = lean_array_push(x_304, x_197);
x_306 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_306, 0, x_188);
lean_ctor_set(x_306, 1, x_7);
lean_ctor_set(x_306, 2, x_305);
x_307 = lean_array_push(x_195, x_306);
x_308 = lean_array_push(x_307, x_282);
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_188);
lean_ctor_set(x_309, 1, x_179);
lean_ctor_set(x_309, 2, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_175);
return x_310;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__1;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__2;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__3;
x_2 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withDeclName", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with_decl_name%", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("?", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declSig", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsafe", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(5u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_matchesNull(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
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
x_22 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_23 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_22, x_16, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Syntax_getOptional_x3f(x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_231; 
x_231 = lean_box(0);
x_25 = x_231;
goto block_230;
}
else
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_24);
if (x_232 == 0)
{
x_25 = x_24;
goto block_230;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_24, 0);
lean_inc(x_233);
lean_dec(x_24);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_25 = x_234;
goto block_230;
}
}
block_230:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_inc(x_16);
x_26 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_16, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_16, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7;
lean_inc(x_4);
x_33 = l_Lean_Name_str___override(x_4, x_32);
x_34 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11;
lean_inc(x_4);
x_35 = l_Lean_Name_str___override(x_4, x_34);
lean_inc(x_27);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11;
lean_inc(x_4);
x_38 = l_Lean_Name_str___override(x_4, x_37);
x_39 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15;
lean_inc(x_30);
lean_inc(x_31);
x_40 = l_Lean_addMacroScope(x_31, x_39, x_30);
x_41 = lean_box(0);
x_42 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14;
lean_inc(x_27);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = l_Lean_Elab_Command_elabDeclaration___closed__7;
lean_inc(x_43);
x_45 = lean_array_push(x_44, x_43);
x_46 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_47 = lean_array_push(x_45, x_46);
x_48 = lean_box(2);
lean_inc(x_38);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
lean_ctor_set(x_49, 2, x_47);
x_50 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16;
lean_inc(x_4);
x_51 = l_Lean_Name_str___override(x_4, x_50);
x_52 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17;
lean_inc(x_5);
x_53 = l_Lean_Name_str___override(x_5, x_52);
x_54 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18;
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19;
lean_inc(x_5);
x_57 = l_Lean_Name_str___override(x_5, x_56);
x_58 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23;
x_59 = l_Lean_addMacroScope(x_31, x_58, x_30);
x_60 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22;
x_61 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25;
lean_inc(x_27);
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_27);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = l_Lean_Elab_Command_elabInductive___closed__1;
lean_inc(x_6);
x_64 = lean_array_push(x_63, x_6);
x_65 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
x_67 = lean_array_push(x_44, x_62);
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_57);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_array_push(x_44, x_55);
lean_inc(x_70);
x_71 = lean_array_push(x_70, x_69);
lean_inc(x_53);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_53);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_array_push(x_63, x_72);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_48);
lean_ctor_set(x_74, 1, x_65);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32;
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_48);
lean_ctor_set(x_77, 1, x_51);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33;
lean_inc(x_4);
x_79 = l_Lean_Name_str___override(x_4, x_78);
x_80 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34;
lean_inc(x_27);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_27);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__5;
lean_inc(x_5);
x_83 = l_Lean_Name_str___override(x_5, x_82);
x_84 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__6;
lean_inc(x_27);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_27);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__7;
lean_inc(x_27);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_27);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_63, x_87);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_48);
lean_ctor_set(x_89, 1, x_65);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35;
lean_inc(x_5);
x_91 = l_Lean_Name_str___override(x_5, x_90);
lean_inc(x_27);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_27);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_44, x_92);
x_94 = lean_array_push(x_93, x_7);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_48);
lean_ctor_set(x_95, 1, x_91);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__8;
x_97 = lean_array_push(x_96, x_85);
x_98 = lean_array_push(x_97, x_89);
lean_inc(x_8);
x_99 = lean_array_push(x_98, x_8);
x_100 = lean_array_push(x_99, x_95);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_48);
lean_ctor_set(x_101, 1, x_83);
lean_ctor_set(x_101, 2, x_100);
x_102 = l_Lean_Elab_Command_elabDeclaration___closed__10;
x_103 = lean_array_push(x_102, x_81);
x_104 = lean_array_push(x_103, x_101);
x_105 = lean_array_push(x_104, x_46);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_48);
lean_ctor_set(x_106, 1, x_79);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36;
x_108 = lean_array_push(x_107, x_36);
x_109 = lean_array_push(x_108, x_49);
x_110 = lean_array_push(x_109, x_77);
x_111 = lean_array_push(x_110, x_106);
x_112 = lean_array_push(x_111, x_46);
x_113 = lean_array_push(x_112, x_46);
x_114 = lean_array_push(x_113, x_46);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_48);
lean_ctor_set(x_115, 1, x_35);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2;
lean_inc(x_5);
x_117 = l_Lean_Name_str___override(x_5, x_116);
x_118 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3;
lean_inc(x_27);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_27);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4;
lean_inc(x_5);
x_121 = l_Lean_Name_str___override(x_5, x_120);
x_122 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5;
x_123 = l_Lean_Name_str___override(x_5, x_122);
x_124 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6;
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_48);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7;
x_127 = l_Lean_Name_str___override(x_9, x_126);
x_128 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8;
x_129 = l_Lean_Name_str___override(x_127, x_128);
x_130 = lean_array_push(x_63, x_43);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_48);
lean_ctor_set(x_131, 1, x_65);
lean_ctor_set(x_131, 2, x_130);
x_132 = lean_array_push(x_44, x_10);
x_133 = lean_array_push(x_132, x_131);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_48);
lean_ctor_set(x_134, 1, x_129);
lean_ctor_set(x_134, 2, x_133);
x_135 = lean_array_push(x_44, x_125);
x_136 = lean_array_push(x_135, x_134);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_48);
lean_ctor_set(x_137, 1, x_121);
lean_ctor_set(x_137, 2, x_136);
x_138 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__9;
lean_inc(x_27);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_44, x_137);
x_141 = lean_array_push(x_140, x_139);
x_142 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9;
lean_inc(x_27);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_27);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_array_push(x_102, x_119);
x_145 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15;
lean_inc(x_4);
x_146 = l_Lean_Name_str___override(x_4, x_145);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_27);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_array_push(x_44, x_8);
x_149 = lean_array_push(x_148, x_46);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_48);
lean_ctor_set(x_150, 1, x_38);
lean_ctor_set(x_150, 2, x_149);
x_151 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__10;
lean_inc(x_4);
x_152 = l_Lean_Name_str___override(x_4, x_151);
x_153 = lean_array_push(x_70, x_6);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_48);
lean_ctor_set(x_154, 1, x_53);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_array_push(x_75, x_154);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_48);
lean_ctor_set(x_156, 1, x_152);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_array_push(x_96, x_147);
x_158 = lean_array_push(x_157, x_150);
x_159 = lean_array_push(x_158, x_156);
x_160 = lean_array_push(x_159, x_46);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_48);
lean_ctor_set(x_161, 1, x_146);
lean_ctor_set(x_161, 2, x_160);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_221; 
lean_dec(x_4);
x_221 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_162 = x_221;
goto block_220;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_15, 0);
lean_inc(x_222);
lean_dec(x_15);
x_223 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11;
x_224 = l_Lean_Name_str___override(x_4, x_223);
x_225 = l_Lean_SourceInfo_fromRef(x_222);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
x_227 = lean_array_push(x_63, x_226);
x_228 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_228, 0, x_48);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_227);
x_229 = lean_array_push(x_63, x_228);
x_162 = x_229;
goto block_220;
}
block_220:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_163 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3;
x_164 = l_Array_append___rarg(x_163, x_162);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_48);
lean_ctor_set(x_165, 1, x_65);
lean_ctor_set(x_165, 2, x_164);
x_166 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__4;
x_167 = lean_array_push(x_166, x_165);
x_168 = lean_array_push(x_167, x_46);
lean_inc(x_11);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_48);
lean_ctor_set(x_169, 1, x_11);
lean_ctor_set(x_169, 2, x_168);
x_170 = lean_array_push(x_44, x_169);
x_171 = lean_array_push(x_170, x_115);
lean_inc(x_33);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_48);
lean_ctor_set(x_172, 1, x_33);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_array_push(x_44, x_172);
if (lean_obj_tag(x_13) == 0)
{
x_174 = x_163;
goto block_217;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_13, 0);
lean_inc(x_218);
lean_dec(x_13);
x_219 = lean_array_push(x_63, x_218);
x_174 = x_219;
goto block_217;
}
block_217:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = l_Array_append___rarg(x_163, x_174);
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_48);
lean_ctor_set(x_176, 1, x_65);
lean_ctor_set(x_176, 2, x_175);
x_177 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10;
x_178 = lean_array_push(x_177, x_176);
if (lean_obj_tag(x_12) == 0)
{
x_179 = x_163;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_12, 0);
lean_inc(x_216);
lean_dec(x_12);
x_179 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_180 = l_Array_append___rarg(x_141, x_179);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_48);
lean_ctor_set(x_181, 1, x_65);
lean_ctor_set(x_181, 2, x_180);
x_182 = lean_array_push(x_144, x_181);
x_183 = lean_array_push(x_182, x_143);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_48);
lean_ctor_set(x_184, 1, x_117);
lean_ctor_set(x_184, 2, x_183);
x_185 = lean_array_push(x_63, x_184);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_48);
lean_ctor_set(x_186, 1, x_65);
lean_ctor_set(x_186, 2, x_185);
x_187 = lean_array_push(x_178, x_186);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_188 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38;
x_189 = lean_array_push(x_187, x_188);
x_190 = lean_array_push(x_189, x_46);
x_191 = lean_array_push(x_190, x_46);
x_192 = lean_array_push(x_191, x_46);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_48);
lean_ctor_set(x_193, 1, x_11);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_array_push(x_44, x_193);
x_195 = lean_array_push(x_194, x_161);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_48);
lean_ctor_set(x_196, 1, x_33);
lean_ctor_set(x_196, 2, x_195);
x_197 = lean_array_push(x_173, x_196);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_48);
lean_ctor_set(x_198, 1, x_65);
lean_ctor_set(x_198, 2, x_197);
if (lean_is_scalar(x_29)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_29;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_28);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_200 = lean_ctor_get(x_25, 0);
lean_inc(x_200);
lean_dec(x_25);
x_201 = lean_array_push(x_163, x_200);
x_202 = l_Array_append___rarg(x_163, x_201);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_48);
lean_ctor_set(x_203, 1, x_65);
lean_ctor_set(x_203, 2, x_202);
x_204 = lean_array_push(x_187, x_203);
x_205 = lean_array_push(x_204, x_46);
x_206 = lean_array_push(x_205, x_46);
x_207 = lean_array_push(x_206, x_46);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_48);
lean_ctor_set(x_208, 1, x_11);
lean_ctor_set(x_208, 2, x_207);
x_209 = lean_array_push(x_44, x_208);
x_210 = lean_array_push(x_209, x_161);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_48);
lean_ctor_set(x_211, 1, x_33);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_array_push(x_173, x_211);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_48);
lean_ctor_set(x_213, 1, x_65);
lean_ctor_set(x_213, 2, x_212);
if (lean_is_scalar(x_29)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_29;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_28);
return x_214;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_matchesNull(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_23 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_22, x_14, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(4u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Syntax_isNone(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1u);
lean_inc(x_25);
x_28 = l_Lean_Syntax_matchesNull(x_25, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_30 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_29, x_14, x_15);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_Lean_Syntax_getArg(x_25, x_20);
lean_dec(x_25);
x_32 = l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11;
lean_inc(x_3);
x_33 = l_Lean_Name_str___override(x_3, x_32);
lean_inc(x_31);
x_34 = l_Lean_Syntax_isOfKind(x_31, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_36 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_35, x_14, x_15);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Lean_Syntax_getArg(x_31, x_20);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Command_expandInitialize___lambda__2(x_1, x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13, x_11, x_39, x_38, x_14, x_15);
lean_dec(x_17);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
x_41 = lean_box(0);
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Command_expandInitialize___lambda__2(x_1, x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13, x_11, x_42, x_41, x_14, x_15);
lean_dec(x_17);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_16);
x_18 = l_Lean_Syntax_matchesNull(x_16, x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_20 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_19, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_16, x_21);
lean_dec(x_16);
x_23 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2;
lean_inc(x_4);
x_24 = l_Lean_Name_str___override(x_4, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_27 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_26, x_13, x_14);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l_Lean_Syntax_getArg(x_22, x_15);
lean_dec(x_22);
x_29 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Command_expandInitialize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_31, x_30, x_13, x_14);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Command_expandInitialize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_34, x_33, x_13, x_14);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docComment", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initialize", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("builtinInit", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_7);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1;
lean_inc(x_2);
x_15 = l_Lean_Name_str___override(x_2, x_14);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Lean_Syntax_getArg(x_6, x_124);
lean_dec(x_6);
x_126 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3;
x_127 = l_Lean_Syntax_isToken(x_126, x_125);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__5;
x_16 = x_128;
goto block_123;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__7;
x_16 = x_129;
goto block_123;
}
block_123:
{
lean_object* x_17; 
x_17 = l_Lean_mkIdentFrom(x_1, x_16);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_9);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_3, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1u);
lean_inc(x_19);
x_22 = l_Lean_Syntax_matchesNull(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_24 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_23, x_10, x_11);
lean_dec(x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = l_Lean_Syntax_getArg(x_19, x_18);
lean_dec(x_19);
x_26 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2;
lean_inc(x_4);
x_27 = l_Lean_Name_str___override(x_4, x_26);
lean_inc(x_25);
x_28 = l_Lean_Syntax_isOfKind(x_25, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_30 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_29, x_10, x_11);
lean_dec(x_3);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_25);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_3, x_4, x_15, x_2, x_17, x_13, x_5, x_32, x_31, x_10, x_11);
lean_dec(x_3);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_3, x_4, x_15, x_2, x_17, x_13, x_5, x_35, x_34, x_10, x_11);
lean_dec(x_3);
return x_36;
}
}
else
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_8, 0);
lean_dec(x_38);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Syntax_getArg(x_3, x_39);
x_41 = l_Lean_Syntax_isNone(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1u);
lean_inc(x_40);
x_43 = l_Lean_Syntax_matchesNull(x_40, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
lean_free_object(x_8);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_44 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_45 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_44, x_10, x_11);
lean_dec(x_3);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = l_Lean_Syntax_getArg(x_40, x_39);
lean_dec(x_40);
x_47 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2;
lean_inc(x_4);
x_48 = l_Lean_Name_str___override(x_4, x_47);
lean_inc(x_46);
x_49 = l_Lean_Syntax_isOfKind(x_46, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_free_object(x_8);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_50 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_51 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_50, x_10, x_11);
lean_dec(x_3);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_ctor_set(x_8, 0, x_46);
x_52 = lean_box(0);
x_53 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_3, x_4, x_15, x_2, x_17, x_13, x_5, x_52, x_8, x_10, x_11);
lean_dec(x_3);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
lean_free_object(x_8);
x_54 = lean_box(0);
x_55 = lean_box(0);
x_56 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_3, x_4, x_15, x_2, x_17, x_13, x_5, x_55, x_54, x_10, x_11);
lean_dec(x_3);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_8);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Syntax_getArg(x_3, x_57);
x_59 = l_Lean_Syntax_isNone(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_unsigned_to_nat(1u);
lean_inc(x_58);
x_61 = l_Lean_Syntax_matchesNull(x_58, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_58);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_62 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_63 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_62, x_10, x_11);
lean_dec(x_3);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = l_Lean_Syntax_getArg(x_58, x_57);
lean_dec(x_58);
x_65 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2;
lean_inc(x_4);
x_66 = l_Lean_Name_str___override(x_4, x_65);
lean_inc(x_64);
x_67 = l_Lean_Syntax_isOfKind(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_68 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_69 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_68, x_10, x_11);
lean_dec(x_3);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_64);
x_71 = lean_box(0);
x_72 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_3, x_4, x_15, x_2, x_17, x_13, x_5, x_71, x_70, x_10, x_11);
lean_dec(x_3);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_58);
x_73 = lean_box(0);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_3, x_4, x_15, x_2, x_17, x_13, x_5, x_74, x_73, x_10, x_11);
lean_dec(x_3);
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_8, 0);
lean_inc(x_76);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_9, 0);
lean_inc(x_3);
x_79 = l_Lean_Syntax_isOfKind(x_3, x_5);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_free_object(x_9);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_80 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_81 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_80, x_10, x_11);
lean_dec(x_3);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Syntax_getArg(x_3, x_82);
x_84 = l_Lean_Syntax_isNone(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_unsigned_to_nat(1u);
lean_inc(x_83);
x_86 = l_Lean_Syntax_matchesNull(x_83, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_83);
lean_free_object(x_9);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_87 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_88 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_87, x_10, x_11);
lean_dec(x_3);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = l_Lean_Syntax_getArg(x_83, x_82);
lean_dec(x_83);
x_90 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2;
lean_inc(x_4);
x_91 = l_Lean_Name_str___override(x_4, x_90);
lean_inc(x_89);
x_92 = l_Lean_Syntax_isOfKind(x_89, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
lean_free_object(x_9);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_93 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_94 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_93, x_10, x_11);
lean_dec(x_3);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_ctor_set(x_9, 0, x_89);
x_95 = lean_box(0);
x_96 = l_Lean_Elab_Command_expandInitialize___lambda__4(x_3, x_3, x_4, x_15, x_78, x_13, x_76, x_2, x_17, x_5, x_95, x_9, x_10, x_11);
lean_dec(x_3);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
lean_free_object(x_9);
x_97 = lean_box(0);
x_98 = lean_box(0);
x_99 = l_Lean_Elab_Command_expandInitialize___lambda__4(x_3, x_3, x_4, x_15, x_78, x_13, x_76, x_2, x_17, x_5, x_98, x_97, x_10, x_11);
lean_dec(x_3);
return x_99;
}
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_9, 0);
lean_inc(x_100);
lean_dec(x_9);
lean_inc(x_3);
x_101 = l_Lean_Syntax_isOfKind(x_3, x_5);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_76);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_102 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_103 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_102, x_10, x_11);
lean_dec(x_3);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Lean_Syntax_getArg(x_3, x_104);
x_106 = l_Lean_Syntax_isNone(x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_unsigned_to_nat(1u);
lean_inc(x_105);
x_108 = l_Lean_Syntax_matchesNull(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_76);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_109 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_110 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_109, x_10, x_11);
lean_dec(x_3);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = l_Lean_Syntax_getArg(x_105, x_104);
lean_dec(x_105);
x_112 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2;
lean_inc(x_4);
x_113 = l_Lean_Name_str___override(x_4, x_112);
lean_inc(x_111);
x_114 = l_Lean_Syntax_isOfKind(x_111, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_111);
lean_dec(x_100);
lean_dec(x_76);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_115 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1;
x_116 = l_Lean_Macro_throwErrorAt___rarg(x_3, x_115, x_10, x_11);
lean_dec(x_3);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_111);
x_118 = lean_box(0);
x_119 = l_Lean_Elab_Command_expandInitialize___lambda__4(x_3, x_3, x_4, x_15, x_100, x_13, x_76, x_2, x_17, x_5, x_118, x_117, x_10, x_11);
lean_dec(x_3);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_105);
x_120 = lean_box(0);
x_121 = lean_box(0);
x_122 = l_Lean_Elab_Command_expandInitialize___lambda__4(x_3, x_3, x_4, x_15, x_100, x_13, x_76, x_2, x_17, x_5, x_121, x_120, x_10, x_11);
lean_dec(x_3);
return x_122;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declModifiers", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_Command_expandInitialize___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initializeKeyword", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_2 = l_Lean_Elab_Command_expandInitialize___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInitialize___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInitialize___closed__6;
x_2 = l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_expandInitialize___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Command_expandInitialize___closed__3;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Command_expandInitialize___closed__5;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_isNone(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(3u);
lean_inc(x_21);
x_24 = l_Lean_Syntax_matchesNull(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Lean_Syntax_getArg(x_21, x_8);
x_28 = l_Lean_Syntax_getArg(x_21, x_14);
lean_dec(x_21);
x_29 = l_Lean_Elab_Command_expandInitialize___closed__7;
lean_inc(x_28);
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = l_Lean_Syntax_getArg(x_28, x_14);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_27);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
x_37 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Command_expandInitialize___lambda__5(x_1, x_36, x_9, x_37, x_10, x_15, x_38, x_34, x_35, x_2, x_3);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_21);
x_40 = lean_box(0);
x_41 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4;
x_42 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6;
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Command_expandInitialize___lambda__5(x_1, x_41, x_9, x_42, x_10, x_15, x_43, x_40, x_40, x_2, x_3);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_expandInitialize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Command_expandInitialize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_expandInitialize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInitialize___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_expandInitialize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandInitialize", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandInitialize), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5;
x_3 = l_Lean_Elab_Command_expandInitialize___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(329u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(341u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__1;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(329u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(329u);
x_2 = lean_unsigned_to_nat(69u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__4;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__5;
x_4 = lean_unsigned_to_nat(69u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_7661_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Inductive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Declaration(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclIdNamespace_x3f___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__5);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__6);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__7);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__8);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__9 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__9);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__10 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__10);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__11);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__12);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__13 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__13);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__14);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__15);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__16 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__16);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__17);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__18);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__19 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__19);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__20);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__21 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__21);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__22);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__23 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__23();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__23);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__24);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__25 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__25();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__25);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___closed__26);
l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1);
l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1 = _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1);
l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2 = _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__1 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__1);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__2 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__2);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__3);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__4 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__4);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__5);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__6 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__6);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__7);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__8 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__8);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__9 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__9);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__10 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__10);
l_Lean_Elab_Command_elabAxiom___lambda__5___closed__11 = _init_l_Lean_Elab_Command_elabAxiom___lambda__5___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__5___closed__11);
l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1 = _init_l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__7___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2();
l_Lean_Elab_Command_elabInductive___closed__1 = _init_l_Lean_Elab_Command_elabInductive___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInductive___closed__1);
l_Lean_Elab_Command_elabClassInductive___closed__1 = _init_l_Lean_Elab_Command_elabClassInductive___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__1);
l_Lean_Elab_Command_elabClassInductive___closed__2 = _init_l_Lean_Elab_Command_elabClassInductive___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__2);
l_Lean_Elab_Command_elabClassInductive___closed__3 = _init_l_Lean_Elab_Command_elabClassInductive___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__3);
l_Lean_Elab_Command_getTerminationHints___closed__1 = _init_l_Lean_Elab_Command_getTerminationHints___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_getTerminationHints___closed__1);
l_Lean_Elab_Command_getTerminationHints___closed__2 = _init_l_Lean_Elab_Command_getTerminationHints___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_getTerminationHints___closed__2);
l_Lean_Elab_Command_getTerminationHints___closed__3 = _init_l_Lean_Elab_Command_getTerminationHints___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_getTerminationHints___closed__3);
l_Lean_Elab_Command_getTerminationHints___closed__4 = _init_l_Lean_Elab_Command_getTerminationHints___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_getTerminationHints___closed__4);
l_Lean_Elab_Command_getTerminationHints___closed__5 = _init_l_Lean_Elab_Command_getTerminationHints___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_getTerminationHints___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabDeclaration___spec__4___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabDeclaration___spec__5___rarg___closed__2);
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
l_Lean_Elab_Command_elabDeclaration___closed__8 = _init_l_Lean_Elab_Command_elabDeclaration___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__8);
l_Lean_Elab_Command_elabDeclaration___closed__9 = _init_l_Lean_Elab_Command_elabDeclaration___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__9);
l_Lean_Elab_Command_elabDeclaration___closed__10 = _init_l_Lean_Elab_Command_elabDeclaration___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__10);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__2);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__4);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__5);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__6);
res = l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___closed__3);
l_Lean_Elab_Command_expandMutualNamespace___closed__1 = _init_l_Lean_Elab_Command_expandMutualNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualNamespace___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace___closed__6);
res = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandMutualElement___closed__1 = _init_l_Lean_Elab_Command_expandMutualElement___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualElement___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement___closed__3);
res = l___regBuiltin_Lean_Elab_Command_expandMutualElement(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandMutualPreamble___closed__1 = _init_l_Lean_Elab_Command_expandMutualPreamble___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualPreamble___closed__1);
l_Lean_Elab_Command_expandMutualPreamble___closed__2 = _init_l_Lean_Elab_Command_expandMutualPreamble___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualPreamble___closed__2);
l_Lean_Elab_Command_expandMutualPreamble___closed__3 = _init_l_Lean_Elab_Command_expandMutualPreamble___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualPreamble___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble___closed__3);
res = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutual___spec__1___closed__2);
l_Lean_Elab_Command_elabMutual___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabMutual___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___lambda__2___closed__1);
l_Lean_Elab_Command_elabMutual___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabMutual___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___lambda__2___closed__2);
l_Lean_Elab_Command_elabMutual___closed__1 = _init_l_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__1);
l_Lean_Elab_Command_elabMutual___closed__2 = _init_l_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__2);
l_Lean_Elab_Command_elabMutual___closed__3 = _init_l_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__3);
l_Lean_Elab_Command_elabMutual___closed__4 = _init_l_Lean_Elab_Command_elabMutual___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__4);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabMutual(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5);
l_Lean_Elab_Command_elabAttr___closed__1 = _init_l_Lean_Elab_Command_elabAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAttr___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAttr___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr___closed__2);
l___regBuiltin_Lean_Elab_Command_elabAttr___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr___closed__3);
l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr___closed__4);
l___regBuiltin_Lean_Elab_Command_elabAttr___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__1);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__2);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__3);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__4);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__5);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__6);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__7);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__8);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__9);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__10);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__11);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__12);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__13 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__13);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__14);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__15);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__16);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__17);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__18);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__19);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__20);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__21 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__21);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__22);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__23);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__24 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__24);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__25);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__26);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__27 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__27);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__28);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__29);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__30 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__30);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__31);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__32);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__33);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__34);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__35);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__36);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__37 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__37);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__38);
l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39 = _init_l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__1___closed__39);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__1 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__1);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__2 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__2);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__3 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__3);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__4 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__4);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__5 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__5);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__6 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__6);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__7 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__7);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__8 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__8);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__9 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__9);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__10 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__10);
l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11 = _init_l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__2___closed__11);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__1);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__2);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__3);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__4 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__4);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__5 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__5);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__6 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__6);
l_Lean_Elab_Command_expandInitialize___lambda__5___closed__7 = _init_l_Lean_Elab_Command_expandInitialize___lambda__5___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___lambda__5___closed__7);
l_Lean_Elab_Command_expandInitialize___closed__1 = _init_l_Lean_Elab_Command_expandInitialize___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__1);
l_Lean_Elab_Command_expandInitialize___closed__2 = _init_l_Lean_Elab_Command_expandInitialize___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__2);
l_Lean_Elab_Command_expandInitialize___closed__3 = _init_l_Lean_Elab_Command_expandInitialize___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__3);
l_Lean_Elab_Command_expandInitialize___closed__4 = _init_l_Lean_Elab_Command_expandInitialize___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__4);
l_Lean_Elab_Command_expandInitialize___closed__5 = _init_l_Lean_Elab_Command_expandInitialize___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__5);
l_Lean_Elab_Command_expandInitialize___closed__6 = _init_l_Lean_Elab_Command_expandInitialize___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__6);
l_Lean_Elab_Command_expandInitialize___closed__7 = _init_l_Lean_Elab_Command_expandInitialize___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandInitialize___closed__7);
l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__1);
l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__2);
l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize___closed__3);
res = l___regBuiltin_Lean_Elab_Command_expandInitialize(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_expandInitialize_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_7661_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
